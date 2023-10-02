import subprocess
import time
import sys
import os
import re

"""
About this file:

- it aims to test elpi vs coq performances of
type class search.

- it should be run from the ./apps/tc folder

- parameters of command line:
    * N : the depth of the tree to build in tests/test.v
    * -nocoq : optional to test only elpi
    * -onlyOne : optional to run the test only for the tree of size N. By default, the tests are made for each i in [1..N] included
"""

INJ_BASE_FUN = "f"
KEYS = "coqT, elpiT, tcSearch, elpi_tc_plus_refine, refineT, compilT, runtimeT".split(", ")


def buildDict():
    res = dict()
    for key in KEYS:
        res[key] = []
    return res


def printDict(d):
    for key in KEYS:
        d[key] = sum(d[key])/len(d[key])
    L = [d[k] for k in KEYS]
    L.append(d["elpiT"] - d["refineT"])
    L.append(d["coqT"] / d["elpiT"])
    L.append(d["elpiT"] / d["coqT"] if d["coqT"] > 0 else 100)
    print(", ".join(map(lambda x: str(round(x, 5)), L)))


def findFloats(s):
    return [float(x) for x in re.findall("\d+\.\d*", s)]


def filterLines(lines):
    validStarts = ["Finished", "Refine", "[elpitime]", "TC search"]
    for line in lines.split("\n"):
        for start in validStarts:
            if line.startswith(start):
                yield line


def parseFile(s):
    # print(s)
    lines = [findFloats(x) for x in filterLines(s)]
    # print(s, lines)
    coqT = lines[0][0]
    tcSearch = lines[1][0]
    refineT = lines[2][0]
    elpiStats = lines[3]
    compilT, runtimeT = elpiStats[0], elpiStats[-1]
    elpiT = lines[4][0]
    elpi_tc_plus_refine = refineT + tcSearch
    res = buildDict()
    for key in KEYS:
        res[key].append(eval(key))
    return res


def buildTree(len):
    if len == 0:
        return INJ_BASE_FUN + " "
    S = buildTree(len-1)
    STR = "(compose " + S + S + ")"
    return STR

accumulate = """
Elpi Accumulate TC_solver lp:{{
:before "999"
  tc {{:gref Inj}} {{Inj lp:R1 lp:R1 (@compose lp:A lp:A lp:A lp:L lp:R)}} Sol :-
    L = R, !,
    tc {{:gref Inj}} {{Inj lp:R1 lp:R1 lp:L}} InjL,
    Sol = {{@compose_inj lp:A lp:A lp:A lp:R1 lp:R1 lp:R1 lp:L lp:L lp:InjL lp:InjL }}.
}}.
"""

sameInjFun = """
Elpi Accumulate TC_solver lp:{{
:before "999"
  tc-Inj A A RA RA {{@compose lp:A lp:A lp:A lp:LC lp:LC}} Sol :- !,
    tc-Inj A A RA RA LC Sol1, 
    coq.typecheck LC TLC ok,
    coq.typecheck Sol1 TSol1 ok,
    Sol = {{
      let sol : lp:TSol1 := lp:Sol1 in 
      let fl : lp:TLC := lp:LC in 
      @compose_inj lp:A lp:A lp:A lp:RA lp:RA lp:RA fl fl sol sol}}.
}}.
Elpi Typecheck TC_solver. 
"""

sameInjFun2 = """
Elpi Accumulate TC_solver lp:{{
:before "999"
tc-Inj A A RA RA {{compose lp:LF lp:LF}} {{@compose_inj lp:A lp:A lp:A lp:RA lp:RA lp:RA lp:LF lp:LF lp:SolLF lp:SolLF}} :- !,
  tc-Inj A A RA RA LF SolLF.
}}.
Elpi Typecheck TC_solver. 
"""

sameInjFun3 = """
Elpi Accumulate TC_solver lp:{{
  :before "999"
  tc-Inj A B RA RB {{@compose lp:A lp:B lp:C lp:LC lp:LC}} {{
      let sol : @Inj lp:A lp:A lp:RA lp:RA lp:LC := lp:Sol1 in 
      let fl : lp:A -> lp:A := lp:LC in 
      @compose_inj lp:A lp:B lp:C lp:RA lp:RA lp:RB fl fl sol sol}} :- 
    tc-Inj A B RA RB LC Sol1.
}}.
Elpi Typecheck TC_solver. 
"""

sameInjFun4 = """
Elpi Accumulate TC_solver lp:{{
  :after "0"
  tc-Inj A B RA RB {{@compose lp:A lp:AB lp:B lp:LC lp:RC}} {{@compose_inj lp:A lp:AB lp:B lp:RA lp:RAB lp:RB lp:LC lp:RC lp:Sol1 lp:Sol2}} :- 
    !,
    tc-Inj A AB RA RAB LC Sol1, 
    tc-Inj AB B RAB RB RC Sol2.

  :after "0"
  tc-Inj _ _ _ _  {{f}} {{h}} :- !.
}}.
Elpi Typecheck TC_solver.  
"""

def writeFile(fileName: str, composeLen: int, isCoq: bool):
    PREAMBLE = f"""\
From elpi.apps.tc.tests Require Import {"stdppInjClassic" if isCoq else "stdppInj"}.
{"" if isCoq else 'Elpi TC_solver. Set TimeRefine. Set TimeTC. Set Debug "elpitime". ' + sameInjFun2}
"""
    GOAL = buildTree(composeLen)
    with open(fileName + ".v", "w") as fd:
        fd.write(PREAMBLE)
        fd.write(f"Goal Inj eq eq({GOAL}). Time apply _. Qed.\n")


def runCoqMake(fileName):
    fileName = fileName + ".vo"
    if (os.path.exists(file_name)):
        subprocess.run(["rm", fileName])
    return subprocess.check_output(["make", fileName]).decode()


def run(file_name, height):
    def partialFun(isCoq: bool):
        writeFile(file_name, height, isCoq)
        return runCoqMake(file_name)
    return partialFun


def loopTreeDepth(file_name: str, maxHeight: int, makeCoq=True, onlyOne=False):
    print("Height, Nodes, Coq, Elpi, TC search, Elpi TC+Refine, Refine, ElpiCompil, ElpiRuntime, ElpiNoRefine, Ratio(Coq/Elpi), Ratio(Elpi/Coq)")
    for i in range(1 if not onlyOne else maxHeight, maxHeight+1):
        FUN = run(file_name, i)
        x = FUN(True) if makeCoq else "Finished 0.0"
        y = FUN(False)
        print(i, ", ", 2 ** i, ", ", end="", sep="")
        dic = parseFile(x + y)
        printDict(dic)


if __name__ == "__main__":
    print(os.curdir)
    file_name = "tests/test"
    height = int(sys.argv[1])
    loopTreeDepth(file_name, height, makeCoq=not (
        "-nocoq" in sys.argv), onlyOne=("-onlyOne" in sys.argv))
    writeFile(file_name, 3, False)

"""
Inductive Method

This file is part of uSMPT.

uSMPT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

uSMPT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with uSMPT. If not, see <https://www.gnu.org/licenses/>.
"""

from __future__ import annotations

__author__ = "Nicolas AMAT, ONERA/DTIS, Université de Toulouse"
__contact__ = "nicolas.amat@onera.fr"
__license__ = "GPLv3"
__version__ = "1.0"

from logging import info
from multiprocessing import Queue
from typing import Optional

from usmpt.checkers.abstractchecker import AbstractChecker
from usmpt.exec.utils import STOP, send_signal_pids, set_verbose
from usmpt.interfaces.z3 import Z3
from usmpt.ptio.verdict import Verdict


class Induction(AbstractChecker):
    """
    Induction method.
    """

    def __init__(self, ptnet, formula, verbose: bool = False, debug=False, solver_pids=None):
        """ Initializer.
        """
        # Initial Petri net
        self.ptnet = ptnet

        # Formula to study
        self.formula = formula

        # Verbosity
        self.verbose = verbose

        # SMT solver
        self.solver = Z3(debug=debug, solver_pids=solver_pids)

    def prove(self, result: Queue[Verdict], concurrent_pids: Queue[list[int]]):
        """ Prover.

        Parameters
        ----------
        result : Queue of Verdict
            Queue to exchange the verdict.
        concurrent_pids : Queue of int
            Queue to get the PIDs of the concurrent methods.
        """
        set_verbose(self.verbose)

        info("[INDUCTION] RUNNING")

        induction = self.prove_helper()

        # Kill the solver
        self.solver.kill()

        # Quit if the solver has aborted
        if self.solver.aborted:
            return

        # Put the result in the queue
        if induction is True:
            result.put(Verdict.REACHABLE)
        elif induction is False:
            result.put(Verdict.NOT_REACHABLE)
        elif induction is None:
            result.put(Verdict.UNKNOWN)

        # Terminate concurrent methods
        if induction is None and not concurrent_pids.empty():
            send_signal_pids(concurrent_pids.get(), STOP)

    ######################
    # TODO: Sect. 2.3.2. #
    ######################
    def prove_helper(self) -> Optional[bool]:
        """ Prover to complete.

        Returns
        -------
        bool, optional
            `True` if the formula is inductive, `None` otherwise.
        """
        info("[INDUCTION] > Initialization")
        
        info("[INDUCTION] > Push")
        self.solver.push()

        info("[INDUCTION] > Declaration of the places from the Petri net (iteration: 0)")
        self.solver.write(self.ptnet.smtlib_declare_places(0))

        info("[INDUCTION] > Initial marking of the Petri net")
        self.solver.write(self.ptnet.smtlib_set_initial_marking(0))

        info("[INDUCTION] > Formula to check the satisfiability (iteration: 0)")
        self.solver.write(self.formula.smtlib(0, assertion=True))

        if self.solver.check_sat():
            info("[INDUCTION] > Pop")
            self.solver.pop()
            return True

        info("[INDUCTION] > Pop")
        self.solver.pop()

        info("[INDUCTION] > Push")
        self.solver.push()

        info("[INDUCTION] > Declaration of the places from the Petri net (iteration: {})".format(0))
        self.solver.write(self.ptnet.smtlib_declare_places(0))
        
        info("[INDUCTION] > Declaration of the places from the Petri net (iteration: {})".format(1))
        self.solver.write(self.ptnet.smtlib_declare_places(1))

        info("[INDUCTION] > Formula to check the satisfiability (iteration: {})".format(0))
        self.solver.write(self.formula.smtlib(0, assertion=True, negation=True))

        info("[INDUCTION] > Transition relation: {} -> {}".format(0, 1))
        self.solver.write(self.ptnet.smtlib_transition_relation(0, 1))

        info("[INDUCTION] > Formula to check the satisfiability (iteration: {})".format(1))
        self.solver.write(self.formula.smtlib(1, assertion=True))

        if self.solver.check_sat():
            info("[INDUCTION] > Pop")
            self.solver.pop()
            return None
        else: 
            info("[INDUCTION] > Pop")
            self.solver.pop()
            return False
    ######################
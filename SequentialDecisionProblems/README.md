# SequentialDecisionProblems (SDPs)

* [CoreTheory](CoreTheory.lidr) The core theory of monadic sequential
  decision problems with a generic implementation of backwards induction
  for computing optimal policy sequences.

* [FullTheory](FullTheory.lidr) The full theory with a machine checkable
  proof that the generic beackwards induction implementation of the core
  theory is correct.

* [AvoidabilityTheory](AvoidabilityTheory.lidr) A tentative theory of
  avoidability: explains what it means for future states to be avoidable
  and under which conditions avoidability is decidable. Work in
  progress.

* [Utils](Utils.lidr) Finiteness and decidability notions, standard
  deduction patterns for the implementation of specific SDPs and
  utilities for the computation of possible state-control trajectories,
  rewards, etc.

* [Helpers](Helpers.lidr) Obsolete, will soon disappear.

* [DeterministicDefaults](DeterministicDefaults.lidr) Defaults for
  deterministic SDPs, see [Example1](examples/Example1.lidr).

* [NonDeterministicDefaults](NonDeterministicDefaults.lidr) Defaults for
  non-deterministic SDPs, see [Example2](examples/Example2.lidr).

* [StochasticDefaults](StochasticDefaults.lidr) Defaults for
  stochastic SDPs, see [Example5](examples/Example5.lidr).

* [OptDefaults.lidr](OptDefaults.lidr) Defaults for solving SDPs with
  finite controls, see examples in [examples](examples/).

* [ViabilityDefaults](ViabilityDefaults.lidr) Default implementation of
  `Viable`. It can be overridden by more efficient, application-specific
  implementations, see for instance [Example5](examples/Example5.lidr)
  vs. [Example5.NoViabilityDEfaults](examples/Example5.NoViabilityDEfaults.lidr).



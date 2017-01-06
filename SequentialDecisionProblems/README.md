# SequentialDecisionProblems (SDPs)

## Files

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

* [TabBackwardsInduction](TabBackwardsInduction.lidr) A tabulated,
  tail-recursive implementation of the generic backwards induction
  algorithm of the core theory, see .Tab examples in (examples/).

* [Helpers](Helpers.lidr) Obsolete, will soon disappear.

* [DeterministicDefaults](DeterministicDefaults.lidr) Defaults for
  deterministic SDPs, see [Example1](examples/Example1.lidr).

* [NonDeterministicDefaults](NonDeterministicDefaults.lidr) Defaults for
  non-deterministic SDPs, see [Example2](examples/Example2.lidr).

* [StochasticDefaults](StochasticDefaults.lidr) Defaults for
  stochastic SDPs, see [Example5](examples/Example5.lidr).

* [CoreTheoryOptDefaults](CoreTheoryOptDefaults.lidr) Defaults for
  solving SDPs with finite controls, see examples in
  [examples](examples/).

* [FullTheoryOptDefaults](FullTheoryOptDefaults.lidr) Defaults for
  solving SDPs with finite controls, see examples in
  [examples](examples/).

* [TabBackwardsInductionOptDefaults](TabBackwardsInductionOptDefaults.lidr)
  Defaults for solving SDPs with finite controls, see examples in
  [examples](examples/).

* [ViabilityDefaults](ViabilityDefaults.lidr) Default implementation of
  `Viable`. It can be overridden by more efficient, application-specific
  implementations, see for instance [Example5](examples/Example5.lidr)
  vs. [Example5.NoViabilityDefaults](examples/Example5.NoViabilityDefaults.lidr).

* [README](README.md) This file


## Timeline

* 2017-01-06: added a tabulated, tail-recursive implementation of the
  generic backwards induction algorithm from the core theory in
  [TabBackwardsInduction](TabBackwardsInduction.lidr) and examples in
  [examples](examples/).
  

## Open questions

* 2017-01-06:

    * Can we express the tabulated, tail-recursive implementation of
       [TabBackwardsInduction](TabBackwardsInduction.lidr) as an
       instance of a general pattern?

    * The examples in [examples](examples/) suggest that, if the
      computation of `Viable` and `Reachable` is efficient (the
      `.NonViabilityDefaults` examples), the tabulated implementation
      indeed executes in liner time in the number of decision steps but
      ...

    * ... the default implementation of `Viable` and, likely, the
      computation of trajectories for non-deterministic and stochastic
      problems can completely spoil this behavior and bring back the
      execution times of the naive implementation from the core theory.

    * Can we re-gain linear complexity by re-implementing `Viable` (and
      the computation of trajectories) in a tabulated, tail-recursive
      form?



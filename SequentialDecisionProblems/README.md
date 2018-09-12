# SequentialDecisionProblems (SDPs)

## Files

* [CoreTheory](CoreTheory.lidr) The core theory of monadic sequential
  decision problems with a generic implementation of backwards induction
  for computing optimal policy sequences.

* [FullTheory](FullTheory.lidr) The full theory with a machine checkable
  proof that the generic backwards induction implementation of the core
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

* [DeterministicDefaults](DeterministicDefaults.lidr) Defaults for
  deterministic SDPs, see [Example1](examples/Example1.lidr).

* [NonDeterministicDefaults](NonDeterministicDefaults.lidr) Defaults for
  non-deterministic SDPs, see [Example2](examples/Example2.lidr).

* [StochasticDefaults](StochasticDefaults.lidr) Defaults for stochastic
  SDPs with probabilities represented by non-negative rational numbers,
  see [Example5](examples/Example5.lidr).

* [FastStochasticDefaults](FastStochasticDefaults.lidr) Defaults for
  stochastic SDPs with probabilities represented by non-negative double
  precision floating point numbers, see
  [Example5](examples/Example5.lidr).

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


## Main concepts (see also CoeGSS's [DSLH](https://gitlab.pik-potsdam.de/botta/IdrisLibs/tree/master/projects/CoeGSS/DSLH.md)) 

* *Monadic dynamical system with control*. The notion of a monadic
  dynamical system with control is at the core of the theory of monadic
  sequential decision problems, see [Sequential decision problems,
  dependent types and generic
  solutions](https://lmcs.episciences.org/3202) and [Contributions to a
  computational theory of policy advice and
  avoidability](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/contributions-to-a-computational-theory-of-policy-advice-and-avoidability/CDB4C9601702AAB336A2FB2C34B8F49B). It
  is formalized through the *hole* (unimplemented element, to be filled
  in by applications) `nexts` in [CoreTheory](CoreTheory.lidr). The
  monad `M` in the signature of `nexts` encodes the uncertainties
  affecting the decision problem. Typically `M = Id` (deterministic
  problem, no uncertainty), `M = List` (non-deterministic problem) or `M = Prob` (stochastic problem).

* *Reachability*. When computing optimal policy sequences, we can
   potentially save a lot of CPU-time by avoiding considering future
   states that cannot be reached by any initial state, see [Sequential
   decision problems, dependent types and generic
   solutions](https://lmcs.episciences.org/3202) and [Contributions to a
   computational theory of policy advice and
   avoidability](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/contributions-to-a-computational-theory-of-policy-advice-and-avoidability/CDB4C9601702AAB336A2FB2C34B8F49B). Technically,
   this is done by restricting the domain of policies (functions that
   maps states to controls, see `Policy` in
   [CoreTheory](CoreTheory.lidr)) to reachable states. The notion of
   reachability is formalized through the *hole* `Reachable` in
   [CoreTheory](CoreTheory.lidr). The idea is that every initial state
   is reachable and that a state `x'` at decision step `t + 1` is
   reachable iff there exists a reachable state `x` at decision step `t`
   and a control that make a transition from `x` to `x'` possible. This
   specification is encoded in the holes `reachableSpec0`,
   `reachableSpec1` and `reachableSpec2` also in
   [CoreTheory](CoreTheory.lidr). Of these, only `reachableSpec1` is
   actually needed in order to apply the theory. The other two are just
   "moral" requirements and can simply be postulated. We support users
   by providing a default definition of `Reachable` that fulfills
   `reachableSpec1` under the assumption that `M` fulfills a natural
   "container monad" condition, see `allElemSpec1` in
   [ReachabilityDefaults](ReachabilityDefaults.lidr).
   
* *Viability*. The notion of viability plays a crucial role in the
  theory of monadic sequential decision problems and, more generally, in
  sustainability science. Informally, a state is viable for `n` decision
  steps iff it is possible to take 'n' decisions starting from that
  state while avoiding "dead-ends" with certainty. In the context of
  sequential decision problems, a dead-end is a state whose
  corresponding set of available controls is empty. We have discussed
  concrete examples of decision problems in which viability is
  constrained in [Sequential decision problems, dependent types and
  generic solutions](https://lmcs.episciences.org/3202) and in
  [Contributions to a computational theory of policy advice and
  avoidability](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/contributions-to-a-computational-theory-of-policy-advice-and-avoidability/CDB4C9601702AAB336A2FB2C34B8F49B). In
  practice, viability is needed to make sure that a decision problem is
  well-posed: the system detects attempts at computing optimal policy
  sequences of length `n` for initial states that are not viable for `n`
  decision steps and rejects such states. Formally, the notion of
  viability is encoded in `Viable` in [CoreTheory](CoreTheory.lidr). As
  for reachability, also `Viable` has to fulfill a specification. If a
  state `x` has a control `y` such that all the states that can be
  obtained by selecting `y` in `x` are viable `n` steps, then `x` is
  viable `n + 1` steps. A default implementation of `Viable` is provided
  in [ViabilityDefaults](ViabilityDefaults.lidr).

* *Avoidability*. In Global Systems Science (GSS), decision makers are
   often faced with the problem of implementing decisions that avoid (or
   avoid with a probability that exceeds a given threshold) certain
   possible future outcomes that are felt to be dangerous, unacceptable
   or, perhaps, just unmanageable. In climate impact research, for
   instance, the notion of avoidability is closely related to that of
   adaptation and mitigation and central to the idea of "avoiding the
   unmanageable" and of "managing the unavoidable". But what does it
   mean for future states to be avoidable? Under which conditions is it
   possible to decide if a state is avoidable or not? How do sets of
   avoidable states look like? Are they well-separated or are they
   entangled with unavoidable states? In
   [AvoidabilityTheory](AvoidabilityTheory.lidr) we lay down the
   preliminaries of a computational theory of avoidability. Again, we
   build upon the notion of monadic dynamical systems, reachability and
   viability and put forward a first notion of avoidability, see
   `AvoidableFrom`. The basic idea is that a future state `x'` is
   avoidable from a "current" state `x` iff there exists a distinct
   alternative state `x''`. The latter is required to be reachable from
   `x` and at least as viable as `x'`. This is clearly a weak notion of
   avoidability: it might happen that the probability of actually
   obtaining an alternative state is very low no matter which decisions
   are taken. But this notion is an important first step towards
   building more refined notions. These will necessarily involve the
   construction of ad hoc rewards for "potentially avoidable" states and
   the computation of optimal "avoidance" policies. Here, again, we see
   that the methods for computing provably optimal policy sequences
   implemented in [CoreTheory](CoreTheory.lidr) and
   [FullTheory](FullTheory.lidr) are crucial for building strong,
   operational notions of "actual" avoidability.
   

## Timeline

* 2017-02-02: cleanup. Removed Double.LTEPostulates and
  Double.LTEProperties.

* 2017-01-19: added an implementation of Newcomb's problem in which
  probabilities are represented by non-negative double precision
  floating point numbers. In spite of the many postulates (see
  [Double.Postulates](Double/Postulates.lidr),
  [Double.LTEPostulates](Double/LTEPostulates.lidr),
  [NonNegDouble.Postulates](NonNegDouble/Postulates.lidr) and
  [FastSimpleProb.Measures](FastSimpleProb/Measures.lidr)), the program
  can be compiled (perhaps a nice proof of concept for erasure?)  and
  executes much faster than the correspondent implementation based on
  non-negative rational numbers, see
  [FastNewcomb](applications/FastNewcomb.lidr)
  vs. [Newcomb](applications/Newcomb.lidr)

* 2017-01-19: added
  [FastStochasticDefaults](FastStochasticDefaults.lidr) for stochastic
  SDPs with probabilities represented by non-negative double precision
  floating point numbers (NonNegDouble) instead of non-negative rational
  numbers (NonNegRational).

* 2017-01-06: added a tabulated, tail-recursive implementation of the
  generic backwards induction algorithm from the core theory in
  [TabBackwardsInduction](TabBackwardsInduction.lidr) and examples in
  [examples](examples/).
  

## Open questions

* 2017-01-19: Can we reduce the number of postulates on double-precision
  floating point numbers necessary for implementing simple probability
  distributions to a minimal number of core postulates? The only feature
  which is actually needed for computations is a decision procedure for
  x <= y for arbitrary (x, y : Double).

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



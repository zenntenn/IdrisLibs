*DSLH*: DSL for determining the structure of the simulation needed to answer a high-level question
--------------------------------------------------------------------------------------------------

This file describes the current implementation of *DSLH*, the DSL for determining the structure of the simulation needed to answer a high-level question.  DSLH is part of the DSLs implemented in Task 3.4 (*Domain-specific languages for generating application-specific synthetic populations for GSS simulations*).  It is presented in the Deliverable 3.4 as follows:

> *DSLH* formalises the high-level concepts of "avoidability", "vulnerability", "reachability", associating to each of these the type of simulations needed to assess it.

> **DSL structure**:

> - front-end: high-level "avoidability", "vulnerability", "reachability"
  - back-end: lists of items needed to assemble the simulation, e.g.
    - the SIS that can be used to determine possible trajectories
    - a *harm* function, that measures damages, losses, etc.\ along a trajectory
    - a *vulnerability measure* that fulfils the monotonicity condition

> **Further references**:  *DSLH* is described in the publications [Vulnerability modelling with functional programming and dependent types](https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/vulnerability-modelling-with-functional-programming-and-dependent-types/C68FE66F3730E7DA26F4FE2F6352EBC9), [@ionescu2016vulnerability], [Sequential decision problems, dependent types and generic solutions](https://lmcs.episciences.org/3202), [@botta2017sequential], [Contributions to a computational theory of policy advice and avoidability](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/contributions-to-a-computational-theory-of-policy-advice-and-avoidability/CDB4C9601702AAB336A2FB2C34B8F49B), [@botta2017contributions].

> **Current status**: The software described in these publications is implemented in the dependently-typed programming language Idris [@brady2017type], and is available at [online](https://github.com/nicolabotta/SeqDecProbs).  A related implementation in the [Agda](http://wiki.portal.chalmers.se/agda) programming language is available at [SeqDecProb_Agda](https://github.com/patrikja/SeqDecProb_Agda).  A collection of application independent Idris libraries that grew out of the SeqDecProbs framework is [IdrisLibs](https://gitlab.pik-potsdam.de/botta/IdrisLibs).

> **Planned developments**: This DSL will not be further developed in CoeGSS, but will be used to guide the implementation of lower level software systems.
A first example application is outlined in the recent paper [The impact of uncertainty on optimal emission policies](https://www.earth-syst-dynam-discuss.net/esd-2017-86/), [@botta2018impact].

We have currently implemented the following high-level concepts: viability, reachability, vulnerability, and avoidability.  Each of these concepts has a computational formalisation that can be found in, respectively
  - [SequentialDecisionProblems/CoreTheory.lidr](https://gitlab.pik-potsdam.de/botta/IdrisLibs/tree/master/SequentialDecisionProblems/CoreTheory.lidr) (for viability and reachability)
  - [SequentialDecisionProblems/AvoidabilityTheory.lidr](https://gitlab.pik-potsdam.de/botta/IdrisLibs/tree/master/SequentialDecisionProblems/AvoidabilityTheory.lidr) (for avoidability)
  - TODO (for vulnerability)

The structure of simulations needed for computations related to these concepts is given by the unimplemented elements ("*holes*") in these files.  They are automatically discovered and highlighted by loading the files in an Idris-aware  editor such  as Emacs.   Examples  of implementing viability and reachability are found in the files [SequentialDecisionProblems/ViabilityDefaults.lidr](https://gitlab.pik-potsdam.de/botta/IdrisLibs/tree/master/SequentialDecisionProblems/ViabilityDefaults.lidr) and [SequentialDecisionProblems/ReachabilityDefaults.lidr](https://gitlab.pik-potsdam.de/botta/IdrisLibs/tree/master/SequentialDecisionProblems/ReachabilityDefaults.lidr), respectively.  For example of applications, see the directory [SequentialDecisionProblems/applications](https://gitlab.pik-potsdam.de/botta/IdrisLibs/tree/master/SequentialDecisionProblems/applications).


The bibliographic references are available below.

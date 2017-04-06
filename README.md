# IdrisLibs

This repository is a first step towards restructuring the code developed
for the computation of Sequential Decision Problems (SDPs) in
[SeqDecProbs](https://github.com/nicolabotta/SeqDecProbs) into a
collection of Idris Libraries. Some related Agda code is available in
[patrikja/SeqDecProb_Agda](https://github.com/patrikja/SeqDecProb_Agda).

## Type checking

With Idris-dev-71b49d3, you should be able to type check all the basic
libraries by entering "make libs" in the top-level repository. With
Idris 1.0, some libraries fail to type check, please see issue #3727 in
[Idris-dev/issues](https://github.com/idris-lang/Idris-dev/issues).


## Research papers

### 2013: SDPs, dependently-typed solutions

Title: Sequential decision problems, dependently-typed solutions.

Authors: [Nicola Botta](https://www.pik-potsdam.de/members/botta/publications), Cezar Ionescu, and Edwin Brady.

Paper: http://ceur-ws.org/Vol-1010/paper-06.pdf

Published in Proceedings of the Conferences on Intelligent Computer
  Mathematics (CICM 2013), "Programming Languages for Mechanized Mathematics
  Systems Workshop (PLMMS)", volume 1010 of CEUR Workshop Proceedings, 2013.

### 2014-2016: SDPs, dependent types and generic solutions

Title: Sequential decision problems, dependent types and generic solutions

Authors: [Nicola Botta](https://www.pik-potsdam.de/members/botta/publications), Patrik Jansson, Cezar Ionescu, David R. Christiansen, Edwin Brady

Paper: https://lmcs.episciences.org/3202

Published in Logical Methods in Computer Science, March 17, 2017, Volume 13, Issue 1

### 2015-2017: Contributions to a computational theory of policy advice and avoidability

Authors: [Nicola Botta](https://www.pik-potsdam.de/members/botta/publications), Patrik Jansson, Cezar Ionescu

* 2016-01-06: Submitted to the Journal of Functional Programming (JFP) Special issue on Dependently Typed Programming. (JFP is a [RoMEO Green journal](http://www.sherpa.ac.uk/romeo/search.php?issn=0956-7968).)
    * [Full text pre-print available](http://www.cse.chalmers.se/~patrikj/papers/CompTheoryPolicyAdviceAvoidability_JFP_2016_preprint.pdf)
* 2016-07: Review verdict: "Reject and resubmit"
* 2016-11-11: Re-submitted to the Journal of Functional Programming (JFP)
    * [Full text pre-print available](http://www.cse.chalmers.se/~patrikj/papers/CompTheoryPolicyAdviceAvoidability_JFP_2016-11_preprint.pdf)
* 2017-03: Review verdict: "Revise and resubmit"

The work was partially supported by the
[GRACeFUL project](https://www.graceful-project.eu/)
(640954, from the call H2020-FETPROACT-2014) and by the
[CoeGSS project](http://coegss.eu/)
(676547, H2020-EINFRA-2015-1) in the context of
Global Systems Science (GSS).
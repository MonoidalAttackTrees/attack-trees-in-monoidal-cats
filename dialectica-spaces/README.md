Dialectica Spaces
-----------------

This is a formalization of dialectica spaces in the two flavors from
Valeria de Paiva's thesis.  The first flavor is DC over Sets and the
second is GC over sets.  We call the latter Dial over sets.

Each type of space requires the notion of a lineale which are
essentially symmetric monoidal closed categories over partially
ordered sets:

- Defined in [lineale.agda](lineale.agda)
- Theorems about lineales can be found in [lineale-thms.agda](lineale-thms.agda)
- Definitions of concrete lineales can be found in [concrete-lineales.agda](concrete-lineales.agda)

Finally, we have the two types of dialectica spaces:

- DC over sets can be found in [DCSets.agda](DCSets.agda)
- Dial over sets can be found in [DialSets.agda](DialSets.agda)

This formalization is in Agda and depends on the [Augusta University
Agda Library](https://github.com/heades/AUGL).  Lastly, this has only
be tested with Agda 2.4.2.4.
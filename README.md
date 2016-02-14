Project Repository: CRII: SHF: A New Foundation for Attack Trees Based on Monoidal Categories
---------------------------------------------------------------------------------------------

Attack trees are a modeling tool used to assess the threat potential
of a security critical system.  They have been used to analyze the
threat potential of the cybersecurity of power grids, wireless
networks, and many others.  Attack trees for real-world security
scenarios can grow to be quite complex and manipulating such large and
complex trees without a formal semantics can be dangerous.  The
intellectual merits of the research are two fold: 1) It develops a new
mathematical semantics of attack trees that is more general than
existing models using the power of linear logic and category theory;
2) It designs a new domain-specific programming language for
conducting threat analysis using attack trees. It is specifically
designed for not only the construction and manipulation of attack
tress, but also for the ability to verify properties of attack trees.
The project's broader significance and importance are that it is the
first to connect threat analysis with software verification using
typed functional programming languages, and it is the first to connect
linear logic to attack trees.

The project's first step is to give attack trees a categorical
semantics in symmetric monoidal categories.  This is a generalization
over the previous models of attack trees, for example, the multiset
and Petri net models are examples of symmetric monoidal categories.
Then based on this semantics, and the connection between linear logic
and symmetric monoidal categories, the project develops a new
statically-typed linear functional programming language called Lina
for Linear Threat Analysis. Types in Lina correspond to attack trees,
and programs between attack trees correspond to semantically valid
transformations of attack trees.  Therefore, designing and
manipulating complex attack trees in Lina provides a higher confidence
that the resulting analysis is correct.

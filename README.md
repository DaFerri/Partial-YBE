GAP algorithms to deal with partial Yang-Baxter maps, and globalisation of partial actions.
The file partialactions.g deals with the formalism of partial group actions and globalisations.
The file partialYB checks conditions on partial solutions to the Yang-Baxter equation.
The file randomgeneration.g generates partial solutions to the Yang-Baxter equation on a random basis, which is easier than constructing them systematically, and useful to test properties and construct examples. It implements two possible methods of generation: 1) random matrices, and then testing whether they are partial solutions; 2) takes a global solutions as an input, and "partializes" it by setting some entries to "undefined", with a given sparsity parameter.

Caution! The three files may depend on each other. It is recommended to load all three of them.

AI Disclosure: The algorithms have been human-tested and debugged, but written in pair with Gemini AI.

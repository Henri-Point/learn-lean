# learn-lean
These are exercises in the Lean programming language which I have completed. I have used Claude in order to suggest the exercises and to find Lemmas and tactics. The code was written by me however.

The completed exercises are:
1. BST.lean: Implementation of a binary search tree in Lean. The invariant is enforced during construction. Insert and member functions are defined. Furthermore, a function toSortedList is defined and it is shown that it exhibits the correct behavior.
2. RLE.lean: A function for the run length encoding of a sequence is defined. Furthermore, a decoding function is defined and it is shown that it is a left inverse.
3. safeGet.lean: An implementation of safeGet is written and it is shown to be equivalent to the definition in the library.
4. Libsodium.lean: We use a C shim and Lean's foreign function interface in order to call a function from Libsodium.

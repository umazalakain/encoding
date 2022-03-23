
# Using ℓ∅ ℓᵢ ℓₒ ℓᵢₒ and nested types instead of usage multiplicities

Lemma \Gamma = \Delta + \Theta -> [[ \Gamma ]] = [[ \Delta ]] + [[ \Theta ]], that is, the encoding of types is carried along context splits.
Context splits on session types are defined as e.g. S = S + End.
Now, in your work, you use types \ell_\emptyset, \ell_i, \ell_o and \ell_#, where the capabilities i, o and # come with the type of the payload, but crucially the capability  \emptyset does not.
In my work on the other hand I have a constructor chan i o t with i as the input multiplicity (0, 1, omega), o as the output multiplicity, and t as the payload type.
That is, even in the case where both i and o are 0, there is still a payload type t. 
That is, totally consumed channels are not unique. 
Context splits on the linear part are then defined as i0 = i1 + i2 -> o0 = o1 + o2 -> chan i0 o0 t = chan i1 o1 t + chan i2 o2 t. 
On the other hand, because the encoding is functional, that is, it returns a unique result, the encoding of the session type End is defined as chan 0 0 \Top. 
It is here where the problem happens, since e.g. a context split on session types ?Int.End = ?Int.End + End will be encoded as chan 0 1 (chan 0 0 \Top) = chan 0 1 (chan 0 0 \Top) + chan 0 0 \Top, which doesn't line up.

I've tried to circumvent the issue by proving that the payload type of totally consumed channels is irrelevant to the well typedness of processes.
Because of send, this requires that you change channel payload types and payload types in sync, which is not really possible.
Another options is of course to switch to a model closer to what you have in your work. 
That would require some rewriting and would depart from what I did for the leftover typing work and the inference work.
I am not entirely sure but I suspect it might also help to reformulate the encoding as a relation, i.e. instead of [[ End ]] = chan 0 0 \Top, we would have a relation -R- such that \forall t. [[ End ]] R chan 0 0 t, and then we would prove that such relation is realisable.
Not entirely sure about this last approach though. 

# Adding support for unrestricted channels

- Using one typing rule for both linear and unrestricted channels:

    Needs of a subusage relation.
    This can take place at the variable selection (on the leaves of typing derivations) or at every branch (as part of context splits).
    
- Using distinct typing rules for linear and unrestricted channels:

    In line with most of literature.
    Easy, but less general.
    
- Using James Wood's work on linear metatheory.

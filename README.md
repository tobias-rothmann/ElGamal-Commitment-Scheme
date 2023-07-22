# Formalizing the ElGamal encryption as a Commitment Scheme in Isabelle/HOL

## Isabelle/HOL
[Isabelle/HOL](https://isabelle.in.tum.de/) is an open-source interactive theorem prover. The version used for this formalization is Isabelle2022 (as of writing this the most recent version).

## Reference Paper
This work is based on the original [paper](https://ieeexplore.ieee.org/document/1057074):  
T. Elgamal, "A public key cryptosystem and a signature scheme based on discrete logarithms," in IEEE Transactions on Information Theory, vol. 31, no. 4, pp. 469-472, July 1985, doi: 10.1109/TIT.1985.1057074.  
However, it is adopted to be a commitment scheme instead of encryption. 

## Concept
The scheme is just like ElGamal encryption based on the Decisional Diffie Hellmann (DDH) Assumption. 
It works on a cyclic group G, in which the DDH assumption holds.
The Scheme works as follows: 
#### key generation
The committer chooses a uniformly random private key s, which is kept secret from the verifier, and a public key g^s, which is given to the verifier (g of course being the generator of G).
#### Commitment 
The commiter chooses a uniformly random y and a group element m of G, to which they want to commit, and computes the commitment (g^y, m^(s*y)) with the opening (s,y).
#### verify 
The verifier verifies a correct commitment with the message m, the opening (s,y) and the commitment (g^y, m^(s*y)), by simply recomputing the commitment from the message and the opening.

## Correctness
#### Proven.

## Security Properties
### Perfect Binding 
The commitment scheme binds perfectly, meaning even for an all-powerful adversary, given the message and the opening, the commitment cannot be resolved to a different message m'=/=m.
#### Proven.
### Computational Hiding 
The commitment scheme is only hiding computationally, meaning proof-wise the hiding game can be/needs to be reduced to the DDH-game.

#### TODO, but almost done and probably easily done.


import AESConcrete.ResidualLinePlaneStepCaps

/-!
The residual-line/plane facade exposes the separate (8,11), (11,8), (11,11)
interfaces and their union with the CoupledPair step interfaces. It does not
establish a new return or complete AES10/14/16 theorem.

Independent uniform retained keys, whitening, omitted final MixColumns and
ordered-distinct reference pairs are fixed for the AES10/14/16 target.
-/

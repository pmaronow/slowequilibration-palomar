# Pinned OpenAI GOE proof providers

Copied from https://github.com/openai/math at commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, Apache-2.0. The source closure has 12 modules / 7,041 lines. Changes: added Lean `module`, made imports/public declarations explicit, redirected local module imports to `SlowEquilibration.Upstream`, and exposed public definitions. Mathematical theorem statements and proofs initially retained; any compatibility edits will be documented below.

Original source SHA-256:

```text
7586ce96089f1dfa38fa8f1400fa552f3715f27f34d8df7b47aebf17c45e8052  lean/OAI/MathematicalPhysics/CriticalSK/BlockEnergy.lean
cfe448a9f5eb8e00c4e549d3620a11f039588fcecedbdf1cfdc300c076597cc6  lean/OAI/MathematicalPhysics/CriticalSK/EdgeAsymptotics.lean
dfbd12587ed892f23e5015448e80e1dff5e37b8731c380746fbfbaf96b100a2d  lean/OAI/MathematicalPhysics/CriticalSK/GOESpectrum.lean
e5b070284e48609ab44244f1d204026dd736f2c40accc79ee480fbefa685d728  lean/OAI/MathematicalPhysics/CriticalSK/GaussianConcentration.lean
d879963daaefaf30a50774201a16fc29184e2eb5e449c6213f559bf43cac7365  lean/OAI/MathematicalPhysics/CriticalSK/GaussianMatrices.lean
eeddc406db5736f7df2a2713917f5d2d203e2d4bca82c9f970de50955622b48c  lean/OAI/MathematicalPhysics/CriticalSK/GaussianMoments.lean
ba60a74de6ce25d60c8697788f6bf6d9dc9cdd4041de970104ecfae3ae9ed981  lean/OAI/MathematicalPhysics/CriticalSK/MinMax.lean
2e3e95c73f734952dab0112d6e6a4b6d420afe80e3902a492f893c62b0b82fd0  lean/OAI/MathematicalPhysics/CriticalSK/PathEnergy.lean
d34ab8717e5ee1785047e91309f9930bc7e491d358a4f5358ecb24bae43b3355  lean/OAI/MathematicalPhysics/CriticalSK/PathSpectra.lean
a9808f8ebcbb16042b0e898795d666e29487aa04a5c9eb406134c624b63bc7a9  lean/OAI/MathematicalPhysics/CriticalSK/Powers.lean
17e1cdb28c02e0ec4e1638ac7db11e2914e8b1fd2c12058fd7329e9a6e6fe6bf  lean/OAI/MathematicalPhysics/CriticalSK/Resolvent.lean
096af3f32ee0e38c6f929960781ed72d6af517bb6205e26cbcc629ea693734b9  lean/OAI/MathematicalPhysics/CriticalSK/TriNoise.lean
```

## Additional regularized determinant providers

The same pinned Apache-2.0 source supplies 10 additional modules / 1,189 original source lines, for actual finite-matrix log-determinant calculus and Frobenius-Lipschitz estimates. These matrix results are reused without importing or claiming their original SK spectral-gap result; the upstream Model file defines its ordinary objects but supplies no theorem as a premise. Module/import/exposure adaptations only. Original hashes:

```text
518d712e2ee22ba2f275ec5fd291fec1f97ef240852004a80bd6c085435f3fcb  lean/OAI/Probability/SKGap/Gaussian/GaussianFiniteIBPError.lean
6419a8cb93a4e18cdad2267129daacf4ec3b4404f6fd1081873a6c941c0485f4  lean/OAI/Probability/SKGap/Gaussian/StandardGaussianProduct.lean
16971549e452e348510a5d39c42094bc62afa493c44f94718ec060670c315302  lean/OAI/Probability/SKGap/Localization/CoordinateDeriv.lean
e11247ba71290f03049e4a87ab9a25f85f73e21ec26447b536a009061078a6a8  lean/OAI/Probability/SKGap/Localization/FrobeniusSq.lean
df2fc9e4ccb277860719890b94648d4f6e37fb49fe09049dfc642fcff8b4a397  lean/OAI/Probability/SKGap/Localization/SymmetricElementaryComm.lean
4b7a42020bf7e47023eae2cb92553a43e619f0662c803d1e111b5b1d1a65d924  lean/OAI/Probability/SKGap/Matrix/MatrixCoordinates.lean
0ca039dac28f26b8b0593f973113f0ccd658e3599e54e9b62c3555d2eb6de53c  lean/OAI/Probability/SKGap/Matrix/MatrixLogDet.lean
cef9dec36cd9adc49a8b2d1c5ae75e6daada8d7fe2e6dd1a57b88d0ac3b9beaa  lean/OAI/Probability/SKGap/Matrix/OpNorm.lean
b99c915b8d249e0478398cf3c0b4831a23f7460f2bd9b59c0f50dabd0c72eb5c  lean/OAI/Probability/SKGap/Matrix/RegularizedLogDet.lean
229af68f09aadf012e531e625a52e5c51094ccf33dd92cf2e9500902b179a39b  lean/OAI/Probability/SKGap/Model.lean
```

## Semicircle density normalization adaptation

`SlowEquilibration/SemicirclePotential.lean` adapts the elementary literal density normalization argument from the same pinned Apache-2.0 source, `lean/OAI/Probability/SKGap/Localization/SemicircleDensity.lean`, SHA-256 `830e8966ea62f0dfdb5de21f4236fafaabcaf557e1fac5d4f0fd28615fbc88b7`. It retains source attribution and independently proves all further resolvent/potential identities by ordinary integration by parts and differentiation under the integral. The whole original module is not vendored.

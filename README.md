# Wiles-Defect
This repository contains the calculations of Chapter 5 in the paper "Wiles defect of Hecke algebras via local-global arguments" (Gebhard Böckle, Chandrashekhar B. Khare, Jeffrey Manning), in which the Venkatesh invariants and the Wiles defect are calculated for some local framed deformation rings. 
A current version of the paper is available here. An earlier version can be found at https://arxiv.org/abs/2108.09729.

The calculations were realized in the Computer Algebra System Macaulay2, which is freely available at http://www2.macaulay2.com/Macaulay2/. 
It is not necessary to install Macaulay2 on your local system to try out the calculations, you can also load them into the Web Interface at https://www.unimelb-macaulay2.cloud.edu.au/#home.

## Files
This Read-me contains a short description of the files, which calculations they contain and what part of the paper they correspond to. This information is also given in the comments of each file.

We have the File "ComputingFittIn512.m2", which contains a small routine that is used in Remark 5.12 of the paper to compute the generators of some Fitting ideals. 

The more extensive calculations appear in the other files. For each of the cases named ($\phi$-uni) and (uni) in Chapter 5 of the paper, there are two variants of code, while the Steinberg case (st) is not represented here, as the calculations for that case were done by hand.

The calculations of the ($\phi$-uni) are described in Section 5.3 of the paper. There are two variants of the code due to the two variants of relations given at the beginning of the Section, variant 1 with the "original" $s_4^{\phi-uni}$ and variant 2 with the "alternative" $s_4^{\phi-uni}$ (named `sp4` in the code in both cases). These are `Unipotent-WithTp-variant1.m2` and `Unipotent-WithTp-variant2.m2`.

Then the calculations of the (uni) case correspond to Section 5.4 of the paper. Here, we need to differentiate two cases for the parameters describing the augmentation point on the generic fiber, namely $s \neq t$ (`Unipotent-variant1.m2`) and $s = t$ (`Unipotent-variant2.m2`).

The outline of all four files is roughly the same: Each file can be executed as a whole, but is structured into several steps, which can also be executed independently.

#### Step 0: Relations
This step corresponds to the calculations done in Section 5.1.. For the ($\phi$-uni)-case, they were done without use of Macaulay2, so this step does not appear in the "WithTp"-files. For the (uni)-case, the step is the same for variants 1 and 2.

#### Step 1: Gorensteinness
($\phi$-uni): The calculations in this step give Lemma 5.19.1. and 5.19.2.

(uni): The calculations in this step confirm Lemma 5.4.3. Furthermore, Lemma 5.27.1 and 5.27.2 are shown/calculated here.

#### Step 2: Generic smoothness
($\phi$-uni): This is Lemma 5.19.3

(uni): For variant 1, this step corresponds to Lemma 5.27.3, but in variant 2, see Remark 5.33 instead.


#### Step 3: The Annihilator of $I_{\infty}$
($\phi$-uni): In this section, Lemma 5.22 and Corollary 5.23 are shown.

(uni): Here, Lemma 5.30 is shown. Furthermore, for variant 1, this shows Proposition 5.31.1, but in variant 2, see Remark 5.33 instead.

#### Step 4: Resolutions
($\phi$-uni): Here, Corollary 5.24. is computed.

(uni): For variant 1, this step gives Proposition 5.31.2, but in variant 2, see Remark 5.33 instead.

#### Step 5: Lattices
($\phi$-uni): This is Corollary 5.25.

(uni): For variant 1, these calculations give Proposition 5.31.3., but in variant 2, see Remark 5.33 instead.

## Other Notes
* For better readability of the code, no greek letters were used as variable names. The variable names $\alpha, \beta, \gamma$ appearing in the paper were replaced by `d, e, f` in the code.
* Early versions of the manuscript contained a sign error in Subsection 5.3, case $\mathcal{I}$. In several places, a factor (s+t) appeared which should be a (s-t). This sign error was corrected only in the version of August 4, 2023.

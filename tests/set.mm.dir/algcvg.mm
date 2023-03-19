include "wcel.mm"
include "ccom.mm"
include "cfv.mm"
include "cc0.mm"
include "cn0.mm"
include "wf.mm"
include "wceq.mm"
include "nn0uz.mm"
include "0zd.mm"
include "id.mm"
include "a1i.mm"
include "algrf.mm"
include "ffvelrni.mm"
include "syl5eqel.mm"
include "fvco3.mm"
include "syl2anc.mm"
include "fco.mm"
include "sylancr.mm"
include "0nn0.mm"
include "sylancl.mm"
include "algr0.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "syl6reqr.mm"
include "cv.mm"
include "wa.mm"
include "wne.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wi.mm"
include "ffvelrnda.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "breq12d.mm"
include "imbi12d.mm"
include "vtoclga.mm"
include "syl.mm"
include "peano2nn0.mm"
include "syl2an.mm"
include "algrp1.mm"
include "sylan.mm"
include "3imtr4d.mm"
include "nn0seqcvgd.mm"
include "eqtr3d.mm"

theorem algcvg
  let vz: setvar z
  let cA: class A
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let cN: class N
  let vk: setvar k
  assume algcvg.1: |- F : S --> S
  assume algcvg.2: |- R = seq 0 ( ( F o. 1st ) , ( NN0 X. { A } ) )
  assume algcvg.3: |- C : S --> NN0
  assume algcvg.4: |- ( z e. S -> ( ( C ` ( F ` z ) ) =/= 0 -> ( C ` ( F ` z ) ) < ( C ` z ) ) )
  assume algcvg.5: |- N = ( C ` A )

  disjoint C z
  disjoint F z
  disjoint R z
  disjoint S z
  disjoint A k
  disjoint C k
  disjoint k z
  disjoint N k
  disjoint R k
  disjoint S k
  assert |- ( A e. S -> ( C ` ( R ` N ) ) = 0 )

  proof
    cA
    cS
    wcel
    #
    cN
    cC
    cR
    ccom
    #
    cfv
    #
    cN
    cR
    cfv
    cC
    cfv
    #
    cc0
    @0
    cn0
    cS
    cR
    wf
    #
    cN
    cn0
    wcel
    @2
    @3
    wceq
    @0
    cA
    cR
    cS
    cF
    cc0
    cn0
    nn0uz
    algcvg.2
    @0
    0zd
    #
    @0
    id
    #
    cS
    cS
    cF
    wf
    @0
    algcvg.1
    a1i
    #
    algrf
    #
    @0
    cN
    cA
    cC
    cfv
    #
    cn0
    algcvg.5
    cS
    cn0
    cA
    cC
    algcvg.3
    ffvelrni
    syl5eqel
    cn0
    cS
    cN
    cC
    cR
    fvco3
    syl2anc
    @0
    vk
    @1
    cN
    @0
    cS
    cn0
    cC
    wf
    @4
    cn0
    cn0
    @1
    wf
    algcvg.3
    @8
    cn0
    cS
    cn0
    cC
    cR
    fco
    sylancr
    @0
    cc0
    @1
    cfv
    #
    @9
    cN
    @0
    @10
    cc0
    cR
    cfv
    #
    cC
    cfv
    #
    @9
    @0
    @4
    cc0
    cn0
    wcel
    @10
    @12
    wceq
    @8
    0nn0
    cn0
    cS
    cc0
    cC
    cR
    fvco3
    sylancl
    @0
    @11
    cA
    cC
    @0
    cA
    cR
    cS
    cF
    cc0
    cn0
    nn0uz
    algcvg.2
    @5
    @6
    algr0
    fveq2d
    eqtrd
    algcvg.5
    syl6reqr
    @0
    vk
    cv
    #
    cn0
    wcel
    #
    wa
    #
    @13
    cR
    cfv
    #
    cF
    cfv
    #
    cC
    cfv
    #
    cc0
    wne
    #
    @18
    @16
    cC
    cfv
    #
    clt
    wbr
    #
    @13
    c1
    caddc
    co
    #
    @1
    cfv
    #
    cc0
    wne
    @23
    @13
    @1
    cfv
    #
    clt
    wbr
    @15
    @16
    cS
    wcel
    @19
    @21
    wi
    #
    @0
    cn0
    cS
    @13
    cR
    @8
    ffvelrnda
    vz
    cv
    #
    cF
    cfv
    #
    cC
    cfv
    #
    cc0
    wne
    #
    @28
    @26
    cC
    cfv
    #
    clt
    wbr
    #
    wi
    @25
    vz
    @16
    cS
    @26
    @16
    wceq
    #
    @29
    @19
    @31
    @21
    @32
    @28
    @18
    cc0
    @32
    @27
    @17
    cC
    @26
    @16
    cF
    fveq2
    fveq2d
    #
    neeq1d
    @32
    @28
    @18
    @30
    @20
    clt
    @33
    @26
    @16
    cC
    fveq2
    breq12d
    imbi12d
    algcvg.4
    vtoclga
    syl
    @15
    @23
    @18
    cc0
    @15
    @23
    @22
    cR
    cfv
    #
    cC
    cfv
    #
    @18
    @0
    @4
    @22
    cn0
    wcel
    @23
    @35
    wceq
    @14
    @8
    @13
    peano2nn0
    cn0
    cS
    @22
    cC
    cR
    fvco3
    syl2an
    @15
    @34
    @17
    cC
    @0
    cA
    cR
    cS
    cF
    @13
    cc0
    cn0
    nn0uz
    algcvg.2
    @5
    @6
    @7
    algrp1
    fveq2d
    eqtrd
    #
    neeq1d
    @15
    @23
    @18
    @24
    @20
    clt
    @36
    @0
    @4
    @14
    @24
    @20
    wceq
    @8
    cn0
    cS
    @13
    cC
    cR
    fvco3
    sylan
    breq12d
    3imtr4d
    nn0seqcvgd
    eqtr3d
end

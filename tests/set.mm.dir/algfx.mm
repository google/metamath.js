include "wcel.mm"
include "cz.mm"
include "cuz.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "cn0.mm"
include "ffvelrni.mm"
include "syl5eqel.mm"
include "nn0zd.mm"
include "wa.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "uzval.mm"
include "eleq2d.mm"
include "pm5.32i.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "imbi2d.mm"
include "eqidd.mm"
include "a1i.mm"
include "eluznn0.mm"
include "sylan.mm"
include "cc0.mm"
include "nn0uz.mm"
include "0zd.mm"
include "id.mm"
include "wf.mm"
include "algrp1.mm"
include "syldan.mm"
include "algrf.mm"
include "ffvelrnda.mm"
include "algcvga.mm"
include "imp.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "vtoclga.mm"
include "sylc.mm"
include "eqtrd.mm"
include "biimprd.mm"
include "expcom.mm"
include "adantl.mm"
include "sylbir.mm"
include "a2d.mm"
include "uzind3.mm"
include "sylbi.mm"
include "ex.mm"
include "com3r.mm"
include "mpd.mm"

theorem algfx
  let vz: setvar z
  let cA: class A
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let cK: class K
  let cN: class N
  let vk: setvar k
  let vm: setvar m
  assume algcvga.1: |- F : S --> S
  assume algcvga.2: |- R = seq 0 ( ( F o. 1st ) , ( NN0 X. { A } ) )
  assume algcvga.3: |- C : S --> NN0
  assume algcvga.4: |- ( z e. S -> ( ( C ` ( F ` z ) ) =/= 0 -> ( C ` ( F ` z ) ) < ( C ` z ) ) )
  assume algcvga.5: |- N = ( C ` A )
  assume algfx.6: |- ( z e. S -> ( ( C ` z ) = 0 -> ( F ` z ) = z ) )

  disjoint C z
  disjoint F z
  disjoint R z
  disjoint S z
  disjoint K z
  disjoint N z
  disjoint A k
  disjoint A m
  disjoint k m
  disjoint C k
  disjoint C m
  disjoint k z
  disjoint m z
  disjoint K m
  disjoint N k
  disjoint N m
  disjoint R k
  disjoint R m
  disjoint S k
  disjoint S m
  assert |- ( A e. S -> ( K e. ( ZZ>= ` N ) -> ( R ` K ) = ( R ` N ) ) )

  proof
    cA
    cS
    wcel
    #
    cN
    cz
    wcel
    #
    cK
    cN
    cuz
    cfv
    #
    wcel
    #
    cK
    cR
    cfv
    #
    cN
    cR
    cfv
    #
    wceq
    #
    wi
    @0
    cN
    @0
    cN
    cA
    cC
    cfv
    cn0
    algcvga.5
    cS
    cn0
    cA
    cC
    algcvga.3
    ffvelrni
    syl5eqel
    #
    nn0zd
    @1
    @3
    @0
    @6
    @1
    @3
    @0
    @6
    wi
    #
    @1
    @3
    wa
    @1
    cK
    cN
    vz
    cv
    #
    cle
    wbr
    vz
    cz
    crab
    #
    wcel
    #
    wa
    @8
    @1
    @3
    @11
    @1
    @2
    @10
    cK
    vz
    cN
    uzval
    #
    eleq2d
    pm5.32i
    @0
    vm
    cv
    #
    cR
    cfv
    #
    @5
    wceq
    #
    wi
    @0
    @5
    @5
    wceq
    #
    wi
    #
    @0
    vk
    cv
    #
    cR
    cfv
    #
    @5
    wceq
    #
    wi
    @0
    @18
    c1
    caddc
    co
    #
    cR
    cfv
    #
    @5
    wceq
    #
    wi
    @8
    vm
    vz
    vk
    cN
    cK
    @13
    cN
    wceq
    #
    @15
    @16
    @0
    @24
    @14
    @5
    @5
    @13
    cN
    cR
    fveq2
    eqeq1d
    imbi2d
    @13
    @18
    wceq
    #
    @15
    @20
    @0
    @25
    @14
    @19
    @5
    @13
    @18
    cR
    fveq2
    eqeq1d
    imbi2d
    @13
    @21
    wceq
    #
    @15
    @23
    @0
    @26
    @14
    @22
    @5
    @13
    @21
    cR
    fveq2
    eqeq1d
    imbi2d
    @13
    cK
    wceq
    #
    @15
    @6
    @0
    @27
    @14
    @4
    @5
    @13
    cK
    cR
    fveq2
    eqeq1d
    imbi2d
    @17
    @1
    @0
    @5
    eqidd
    a1i
    @1
    @18
    @10
    wcel
    #
    wa
    #
    @0
    @20
    @23
    @29
    @1
    @18
    @2
    wcel
    #
    wa
    @0
    @20
    @23
    wi
    #
    wi
    #
    @1
    @30
    @28
    @1
    @2
    @10
    @18
    @12
    eleq2d
    pm5.32i
    @30
    @32
    @1
    @0
    @30
    @31
    @0
    @30
    wa
    #
    @23
    @20
    @33
    @22
    @19
    @5
    @33
    @22
    @19
    cF
    cfv
    #
    @19
    @0
    @30
    @18
    cn0
    wcel
    #
    @22
    @34
    wceq
    @0
    cN
    cn0
    wcel
    @30
    @35
    @7
    @18
    cN
    eluznn0
    sylan
    #
    @0
    cA
    cR
    cS
    cF
    @18
    cc0
    cn0
    nn0uz
    algcvga.2
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
    algcvga.1
    a1i
    #
    algrp1
    syldan
    @33
    @19
    cS
    wcel
    #
    @19
    cC
    cfv
    #
    cc0
    wceq
    #
    @34
    @19
    wceq
    #
    @0
    @30
    @35
    @40
    @36
    @0
    cn0
    cS
    @18
    cR
    @0
    cA
    cR
    cS
    cF
    cc0
    cn0
    nn0uz
    algcvga.2
    @37
    @38
    @39
    algrf
    ffvelrnda
    syldan
    @0
    @30
    @42
    vz
    cA
    cC
    cR
    cS
    cF
    @18
    cN
    algcvga.1
    algcvga.2
    algcvga.3
    algcvga.4
    algcvga.5
    algcvga
    imp
    @9
    cC
    cfv
    #
    cc0
    wceq
    #
    @9
    cF
    cfv
    #
    @9
    wceq
    #
    wi
    @42
    @43
    wi
    vz
    @19
    cS
    @9
    @19
    wceq
    #
    @45
    @42
    @47
    @43
    @48
    @44
    @41
    cc0
    @9
    @19
    cC
    fveq2
    eqeq1d
    @48
    @46
    @34
    @9
    @19
    @9
    @19
    cF
    fveq2
    @48
    id
    eqeq12d
    imbi12d
    algfx.6
    vtoclga
    sylc
    eqtrd
    eqeq1d
    biimprd
    expcom
    adantl
    sylbir
    a2d
    uzind3
    sylbi
    ex
    com3r
    mpd
end

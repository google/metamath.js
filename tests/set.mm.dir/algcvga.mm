include "wcel.mm"
include "cn0.mm"
include "cuz.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wi.mm"
include "ffvelrni.mm"
include "syl5eqel.mm"
include "cz.mm"
include "nn0z.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "eluz1.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "imbi2d.mm"
include "algcvg.mm"
include "a1i.mm"
include "w3a.mm"
include "nn0ge0.mm"
include "adantr.mm"
include "cr.mm"
include "nn0re.mm"
include "zre.mm"
include "0re.mm"
include "letr.mm"
include "mp3an1.mm"
include "syl2an.mm"
include "mpand.mm"
include "elnn0z.mm"
include "simplbi2.mm"
include "adantl.mm"
include "syld.mm"
include "sylan.mm"
include "impr.mm"
include "expcom.mm"
include "3adant1.mm"
include "ancld.mm"
include "nn0uz.mm"
include "0zd.mm"
include "id.mm"
include "wf.mm"
include "algrf.mm"
include "ffvelrnda.mm"
include "wne.mm"
include "clt.mm"
include "neeq1d.mm"
include "breq12d.mm"
include "imbi12d.mm"
include "vtoclga.mm"
include "algcvgb.mm"
include "simpr.mm"
include "syl6bi.mm"
include "mpd.mm"
include "syl.mm"
include "algrp1.mm"
include "sylibrd.mm"
include "syl6.mm"
include "a2d.mm"
include "uzind.mm"
include "3expib.mm"
include "sylbid.mm"
include "com3r.mm"

theorem algcvga
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

  disjoint C z
  disjoint F z
  disjoint R z
  disjoint S z
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
  assert |- ( A e. S -> ( K e. ( ZZ>= ` N ) -> ( C ` ( R ` K ) ) = 0 ) )

  proof
    cA
    cS
    wcel
    #
    cN
    cn0
    wcel
    #
    cK
    cN
    cuz
    cfv
    wcel
    #
    cK
    cR
    cfv
    #
    cC
    cfv
    #
    cc0
    wceq
    #
    wi
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
    @1
    @2
    @0
    @5
    @1
    cN
    cz
    wcel
    #
    @2
    @0
    @5
    wi
    #
    wi
    cN
    nn0z
    @7
    @2
    cK
    cz
    wcel
    #
    cN
    cK
    cle
    wbr
    #
    wa
    @8
    cN
    cK
    eluz1
    @7
    @9
    @10
    @8
    @0
    vm
    cv
    #
    cR
    cfv
    #
    cC
    cfv
    #
    cc0
    wceq
    #
    wi
    @0
    cN
    cR
    cfv
    #
    cC
    cfv
    #
    cc0
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
    cC
    cfv
    #
    cc0
    wceq
    #
    wi
    @0
    @19
    c1
    caddc
    co
    #
    cR
    cfv
    #
    cC
    cfv
    #
    cc0
    wceq
    #
    wi
    @8
    vm
    vk
    cN
    cK
    @11
    cN
    wceq
    #
    @14
    @17
    @0
    @27
    @13
    @16
    cc0
    @27
    @12
    @15
    cC
    @11
    cN
    cR
    fveq2
    fveq2d
    eqeq1d
    imbi2d
    @11
    @19
    wceq
    #
    @14
    @22
    @0
    @28
    @13
    @21
    cc0
    @28
    @12
    @20
    cC
    @11
    @19
    cR
    fveq2
    fveq2d
    eqeq1d
    imbi2d
    @11
    @23
    wceq
    #
    @14
    @26
    @0
    @29
    @13
    @25
    cc0
    @29
    @12
    @24
    cC
    @11
    @23
    cR
    fveq2
    fveq2d
    eqeq1d
    imbi2d
    @11
    cK
    wceq
    #
    @14
    @5
    @0
    @30
    @13
    @4
    cc0
    @30
    @12
    @3
    cC
    @11
    cK
    cR
    fveq2
    fveq2d
    eqeq1d
    imbi2d
    @18
    @7
    vz
    cA
    cC
    cR
    cS
    cF
    cN
    algcvga.1
    algcvga.2
    algcvga.3
    algcvga.4
    algcvga.5
    algcvg
    a1i
    @7
    @19
    cz
    wcel
    #
    cN
    @19
    cle
    wbr
    #
    w3a
    #
    @0
    @22
    @26
    @33
    @0
    @0
    @19
    cn0
    wcel
    #
    wa
    #
    @22
    @26
    wi
    @33
    @0
    @34
    @31
    @32
    @0
    @34
    wi
    @7
    @0
    @31
    @32
    wa
    @34
    @0
    @31
    @32
    @34
    @0
    @1
    @31
    @32
    @34
    wi
    @6
    @1
    @31
    wa
    #
    @32
    cc0
    @19
    cle
    wbr
    #
    @34
    @36
    cc0
    cN
    cle
    wbr
    #
    @32
    @37
    @1
    @38
    @31
    cN
    nn0ge0
    adantr
    @1
    cN
    cr
    wcel
    #
    @19
    cr
    wcel
    #
    @38
    @32
    wa
    @37
    wi
    #
    @31
    cN
    nn0re
    @19
    zre
    cc0
    cr
    wcel
    @39
    @40
    @41
    0re
    cc0
    cN
    @19
    letr
    mp3an1
    syl2an
    mpand
    @31
    @37
    @34
    wi
    @1
    @34
    @31
    @37
    @19
    elnn0z
    simplbi2
    adantl
    syld
    sylan
    impr
    expcom
    3adant1
    ancld
    @35
    @22
    @20
    cF
    cfv
    #
    cC
    cfv
    #
    cc0
    wceq
    #
    @26
    @35
    @20
    cS
    wcel
    #
    @22
    @44
    wi
    #
    @0
    cn0
    cS
    @19
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
    algrf
    ffvelrnda
    @45
    @43
    cc0
    wne
    #
    @43
    @21
    clt
    wbr
    #
    wi
    #
    @46
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
    @55
    @53
    cC
    cfv
    #
    clt
    wbr
    #
    wi
    @52
    vz
    @20
    cS
    @53
    @20
    wceq
    #
    @56
    @50
    @58
    @51
    @59
    @55
    @43
    cc0
    @59
    @54
    @42
    cC
    @53
    @20
    cF
    fveq2
    fveq2d
    #
    neeq1d
    @59
    @55
    @43
    @57
    @21
    clt
    @60
    @53
    @20
    cC
    fveq2
    breq12d
    imbi12d
    algcvga.4
    vtoclga
    @45
    @52
    @21
    cc0
    wne
    @51
    wi
    #
    @46
    wa
    @46
    cC
    cS
    cF
    @20
    algcvga.1
    algcvga.3
    algcvgb
    @61
    @46
    simpr
    syl6bi
    mpd
    syl
    @35
    @25
    @43
    cc0
    @35
    @24
    @42
    cC
    @0
    cA
    cR
    cS
    cF
    @19
    cc0
    cn0
    nn0uz
    algcvga.2
    @47
    @48
    @49
    algrp1
    fveq2d
    eqeq1d
    sylibrd
    syl6
    a2d
    uzind
    3expib
    sylbid
    syl
    com3r
    mpd
end

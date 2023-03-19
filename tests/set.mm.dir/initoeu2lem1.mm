include "cv.mm"
include "co.mm"
include "wcel.mm"
include "weu.mm"
include "w3a.mm"
include "cop.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "csn.mm"
include "wex.mm"
include "eusn.mm"
include "cinv.mm"
include "cfv.mm"
include "eqid.mm"
include "ccat.mm"
include "ad2antrr.mm"
include "simpr2.mm"
include "adantr.mm"
include "simpr1.mm"
include "invf.mm"
include "simpr.mm"
include "ffvelrnd.mm"
include "wss.mm"
include "isohom.mm"
include "sselda.mm"
include "ad4antr.mm"
include "simpr3.mm"
include "simplr.mm"
include "catcocl.mm"
include "exp31.mm"
include "imp.mm"
include "wb.mm"
include "eleq2.mm"
include "adantl.mm"
include "cvv.mm"
include "ovex.mm"
include "elsng.mm"
include "mp1i.mm"
include "bitrd.mm"
include "eqeq2.mm"
include "eqcoms.mm"
include "simp-4l.mm"
include "simp-4r.mm"
include "simprr.mm"
include "simprl.mm"
include "initoeu2lem0.mm"
include "syl131anc.mm"
include "exp43.mm"
include "sylbid.mm"
include "ex.mm"
include "com23.mm"
include "com24.mm"
include "syld.mm"
include "com25.mm"
include "mpd.mm"
include "mpdan.mm"
include "com15.mm"
include "impcom.mm"
include "com13.mm"
include "expimpd.mm"
include "3impia.mm"
include "com12.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "3impib.mm"

theorem initoeu2lem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cX: class X
  let c.op: class .o.
  let va: setvar a
  let vg: setvar g
  let vb: setvar b
  assume initoeu1.c: |- ( ph -> C e. Cat )
  assume initoeu1.a: |- ( ph -> A e. ( InitO ` C ) )
  assume initoeu2lem.x: |- X = ( Base ` C )
  assume initoeu2lem.h: |- H = ( Hom ` C )
  assume initoeu2lem.i: |- I = ( Iso ` C )
  assume initoeu2lem.o: |- .o. = ( comp ` C )

  disjoint D f
  disjoint F f
  disjoint G f
  disjoint I f
  disjoint K f
  disjoint H f
  disjoint X f
  disjoint .o. f
  disjoint A f
  disjoint B f
  disjoint C f
  disjoint f ph
  disjoint A a
  disjoint A g
  disjoint a g
  disjoint A b
  disjoint b f
  disjoint B a
  disjoint B g
  disjoint B b
  disjoint C b
  disjoint C a
  disjoint C g
  disjoint g ph
  disjoint f g
  disjoint a f
  assert |- ( ( ph /\ ( A e. X /\ B e. X /\ D e. X ) /\ ( K e. ( B I A ) /\ ( F ( <. B , A >. .o. D ) K ) e. ( B H D ) ) ) -> ( ( E! f f e. ( A H D ) /\ F e. ( A H D ) /\ G e. ( B H D ) ) -> G = ( F ( <. B , A >. .o. D ) K ) ) )

  proof
    vf
    cv
    #
    cA
    cD
    cH
    co
    #
    wcel
    vf
    weu
    #
    cF
    @1
    wcel
    #
    cG
    cB
    cD
    cH
    co
    #
    wcel
    #
    w3a
    wph
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cD
    cX
    wcel
    #
    w3a
    #
    cK
    cB
    cA
    cI
    co
    #
    wcel
    #
    cF
    cK
    cB
    cA
    cop
    cD
    c.op
    co
    co
    #
    @4
    wcel
    #
    wa
    #
    w3a
    #
    cG
    @12
    wceq
    #
    @2
    @3
    @5
    @15
    @16
    wi
    #
    @2
    @1
    @0
    csn
    #
    wceq
    #
    vf
    wex
    @3
    @5
    wa
    #
    @17
    wi
    #
    vf
    @1
    eusn
    @19
    @21
    vf
    @19
    @20
    @17
    @15
    @19
    @20
    wa
    #
    @16
    wph
    @9
    @14
    @22
    @16
    wi
    #
    wph
    @9
    wa
    #
    @11
    @13
    @23
    @24
    @11
    wa
    #
    cK
    cB
    cA
    cC
    cinv
    cfv
    #
    co
    #
    cfv
    #
    cA
    cB
    cI
    co
    #
    wcel
    #
    @13
    @23
    wi
    @25
    @10
    @29
    cK
    @27
    @25
    cX
    cC
    cI
    @26
    cB
    cA
    initoeu2lem.x
    @26
    eqid
    wph
    cC
    ccat
    wcel
    #
    @9
    @11
    initoeu1.c
    ad2antrr
    @24
    @7
    @11
    wph
    @6
    @7
    @8
    simpr2
    #
    adantr
    @24
    @6
    @11
    wph
    @6
    @7
    @8
    simpr1
    #
    adantr
    initoeu2lem.i
    invf
    @24
    @11
    simpr
    ffvelrnd
    @22
    @13
    @25
    @30
    wa
    #
    @16
    @20
    @19
    @13
    @34
    @16
    wi
    wi
    #
    @3
    @5
    @19
    @35
    wi
    @34
    @5
    @19
    @13
    @3
    @16
    @34
    @28
    cA
    cB
    cH
    co
    #
    wcel
    #
    @5
    @19
    @13
    @3
    @16
    wi
    #
    wi
    wi
    #
    wi
    @25
    @29
    @36
    @28
    @24
    @29
    @36
    wss
    @11
    @24
    cX
    cC
    cH
    cI
    cA
    cB
    initoeu2lem.x
    initoeu2lem.h
    initoeu2lem.i
    wph
    @31
    @9
    initoeu1.c
    adantr
    #
    @33
    @32
    isohom
    adantr
    sselda
    @34
    @37
    wa
    #
    @5
    @39
    @41
    @5
    wa
    #
    cG
    @28
    cA
    cB
    cop
    cD
    c.op
    co
    #
    co
    #
    @1
    wcel
    #
    @39
    @42
    cX
    cC
    c.op
    @28
    cG
    cH
    cA
    cB
    cD
    initoeu2lem.x
    initoeu2lem.h
    initoeu2lem.o
    @24
    @31
    @11
    @30
    @37
    @5
    @40
    ad4antr
    @24
    @6
    @11
    @30
    @37
    @5
    @33
    ad4antr
    @24
    @7
    @11
    @30
    @37
    @5
    @32
    ad4antr
    @24
    @8
    @11
    @30
    @37
    @5
    wph
    @6
    @7
    @8
    simpr3
    #
    ad4antr
    @34
    @37
    @5
    simplr
    @41
    @5
    simpr
    catcocl
    @41
    @5
    @45
    @39
    wi
    @41
    @13
    @45
    @19
    @5
    @38
    @41
    @13
    @12
    @28
    @43
    co
    #
    @1
    wcel
    #
    @45
    @19
    @5
    @38
    wi
    #
    wi
    wi
    #
    @34
    @37
    @13
    @48
    wi
    #
    @24
    @37
    @51
    wi
    @11
    @30
    @24
    @37
    @13
    @48
    @24
    @37
    wa
    #
    @13
    wa
    cX
    cC
    c.op
    @28
    @12
    cH
    cA
    cB
    cD
    initoeu2lem.x
    initoeu2lem.h
    initoeu2lem.o
    @24
    @31
    @37
    @13
    @40
    ad2antrr
    @24
    @6
    @37
    @13
    @33
    ad2antrr
    @24
    @7
    @37
    @13
    @32
    ad2antrr
    @24
    @8
    @37
    @13
    @46
    ad2antrr
    @24
    @37
    @13
    simplr
    @52
    @13
    simpr
    catcocl
    exp31
    ad2antrr
    imp
    @34
    @48
    @50
    wi
    @37
    @34
    @19
    @45
    @48
    @49
    @34
    @19
    @45
    @48
    @49
    wi
    wi
    @34
    @19
    wa
    #
    @48
    @45
    @49
    @53
    @48
    @47
    @0
    wceq
    #
    @45
    @49
    wi
    @53
    @48
    @47
    @18
    wcel
    #
    @54
    @19
    @48
    @55
    wb
    @34
    @1
    @18
    @47
    eleq2
    adantl
    @47
    cvv
    wcel
    @55
    @54
    wb
    @53
    @12
    @28
    @43
    ovex
    @47
    @0
    cvv
    elsng
    mp1i
    bitrd
    @53
    @45
    @54
    @49
    @53
    @45
    @44
    @0
    wceq
    #
    @54
    @49
    wi
    #
    @19
    @45
    @56
    wb
    @34
    @19
    @45
    @44
    @18
    wcel
    #
    @56
    @1
    @18
    @44
    eleq2
    @44
    cvv
    wcel
    @58
    @56
    wb
    @19
    cG
    @28
    @43
    ovex
    @44
    @0
    cvv
    elsng
    mp1i
    bitrd
    adantl
    @34
    @56
    @57
    wi
    @19
    @34
    @56
    @57
    @34
    @56
    wa
    @54
    @47
    @44
    wceq
    #
    @49
    @56
    @54
    @59
    wb
    #
    @34
    @60
    @0
    @44
    @0
    @44
    @47
    eqeq2
    eqcoms
    adantl
    @34
    @59
    @49
    wi
    @56
    @34
    @59
    @5
    @3
    @16
    @34
    @59
    wa
    #
    @5
    @3
    wa
    #
    wa
    @24
    @11
    @3
    @5
    @59
    @16
    @24
    @11
    @30
    @59
    @62
    simp-4l
    @24
    @11
    @30
    @59
    @62
    simp-4r
    @61
    @5
    @3
    simprr
    @61
    @5
    @3
    simprl
    @34
    @59
    @62
    simplr
    wph
    cA
    cB
    cC
    cD
    cF
    cG
    cH
    cI
    cK
    cX
    c.op
    initoeu1.c
    initoeu1.a
    initoeu2lem.x
    initoeu2lem.h
    initoeu2lem.i
    initoeu2lem.o
    initoeu2lem0
    syl131anc
    exp43
    adantr
    sylbid
    ex
    adantr
    sylbid
    com23
    sylbid
    com23
    ex
    com24
    adantr
    syld
    com25
    imp
    mpd
    ex
    mpdan
    com15
    imp
    impcom
    com13
    mpdan
    expimpd
    3impia
    com12
    ex
    exlimiv
    sylbi
    3impib
    com12
end

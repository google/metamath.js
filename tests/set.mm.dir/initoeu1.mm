include "cbs.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "chom.mm"
include "co.mm"
include "weu.mm"
include "wral.mm"
include "wa.mm"
include "ciso.mm"
include "cinito.mm"
include "eqid.mm"
include "isinitoi.mm"
include "mpdan.mm"
include "wi.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "eubidv.mm"
include "rspcv.mm"
include "wss.mm"
include "wex.mm"
include "ccat.mm"
include "adantr.mm"
include "simprr.mm"
include "simprl.mm"
include "isohom.mm"
include "euex.mm"
include "a1i.mm"
include "rspcva.mm"
include "syl.mm"
include "ex.mm"
include "ad2antll.mm"
include "cinv.mm"
include "ad2antrr.mm"
include "wbr.mm"
include "2initoinv.mm"
include "3exp.mm"
include "imp31.mm"
include "inviso1.mm"
include "eximdv.mm"
include "expcom.mm"
include "exlimiv.mm"
include "com3l.mm"
include "impd.mm"
include "syl2and.mm"
include "imp.mm"
include "euelss.mm"
include "syl3anc.mm"
include "exp42.mm"
include "com24.mm"
include "com14.mm"
include "expd.mm"
include "syldc.mm"
include "com15.mm"
include "mpd.mm"

theorem initoeu1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let va: setvar a
  let vg: setvar g
  let vb: setvar b
  assume initoeu1.c: |- ( ph -> C e. Cat )
  assume initoeu1.a: |- ( ph -> A e. ( InitO ` C ) )
  assume initoeu1.b: |- ( ph -> B e. ( InitO ` C ) )

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
  assert |- ( ph -> E! f f e. ( A ( Iso ` C ) B ) )

  proof
    wph
    cA
    cC
    cbs
    cfv
    #
    wcel
    #
    vf
    cv
    #
    cA
    vb
    cv
    #
    cC
    chom
    cfv
    #
    co
    #
    wcel
    #
    vf
    weu
    #
    vb
    @0
    wral
    #
    wa
    #
    @2
    cA
    cB
    cC
    ciso
    cfv
    #
    co
    #
    wcel
    #
    vf
    weu
    #
    wph
    cA
    cC
    cinito
    cfv
    #
    wcel
    @9
    initoeu1.a
    wph
    @0
    cC
    vf
    @4
    cA
    vb
    @0
    eqid
    #
    @4
    eqid
    #
    initoeu1.c
    isinitoi
    mpdan
    wph
    @1
    @8
    @13
    wph
    cB
    @0
    wcel
    #
    vg
    cv
    #
    cB
    va
    cv
    #
    @4
    co
    #
    wcel
    #
    vg
    weu
    #
    va
    @0
    wral
    #
    wa
    #
    @1
    @8
    @13
    wi
    wi
    #
    wph
    cB
    @14
    wcel
    @24
    initoeu1.b
    wph
    @0
    cC
    vg
    @4
    cB
    va
    @15
    @16
    initoeu1.c
    isinitoi
    mpdan
    wph
    @17
    @23
    @25
    @8
    @17
    @23
    @1
    wph
    @13
    @17
    @8
    @2
    cA
    cB
    @4
    co
    #
    wcel
    #
    vf
    weu
    #
    @23
    @1
    wph
    @13
    wi
    wi
    #
    wi
    @7
    @28
    vb
    cB
    @0
    @3
    cB
    wceq
    #
    @6
    @27
    vf
    @30
    @5
    @26
    @2
    @3
    cB
    cA
    @4
    oveq2
    eleq2d
    eubidv
    rspcv
    @17
    @28
    @23
    @29
    wph
    @28
    @23
    wa
    #
    @1
    @17
    @13
    wph
    @17
    @1
    @31
    @13
    wph
    @17
    @1
    @31
    @13
    wph
    @17
    @1
    wa
    #
    wa
    #
    @31
    wa
    @11
    @26
    wss
    #
    @12
    vf
    wex
    #
    @28
    @13
    @33
    @34
    @31
    @33
    @0
    cC
    @4
    @10
    cA
    cB
    @15
    @16
    @10
    eqid
    #
    wph
    cC
    ccat
    wcel
    #
    @32
    initoeu1.c
    adantr
    #
    wph
    @17
    @1
    simprr
    #
    wph
    @17
    @1
    simprl
    #
    isohom
    adantr
    @33
    @31
    @35
    @33
    @28
    @27
    vf
    wex
    #
    @23
    @18
    cB
    cA
    @4
    co
    #
    wcel
    #
    vg
    wex
    #
    @35
    @28
    @41
    wi
    @33
    @27
    vf
    euex
    a1i
    @1
    @23
    @44
    wi
    wph
    @17
    @1
    @23
    @44
    @1
    @23
    wa
    @43
    vg
    weu
    #
    @44
    @22
    @45
    va
    cA
    @0
    @19
    cA
    wceq
    #
    @21
    @43
    vg
    @46
    @20
    @42
    @18
    @19
    cA
    cB
    @4
    oveq2
    eleq2d
    eubidv
    rspcva
    @43
    vg
    euex
    syl
    ex
    ad2antll
    @33
    @41
    @44
    @35
    @44
    @33
    @41
    @35
    @43
    @33
    @41
    @35
    wi
    #
    wi
    vg
    @33
    @43
    @47
    @33
    @43
    wa
    #
    @27
    @12
    vf
    @48
    @27
    @12
    @48
    @27
    wa
    @0
    cC
    @2
    @18
    @10
    cC
    cinv
    cfv
    #
    cA
    cB
    @15
    @49
    eqid
    @33
    @37
    @43
    @27
    @38
    ad2antrr
    @33
    @1
    @43
    @27
    @39
    ad2antrr
    @33
    @17
    @43
    @27
    @40
    ad2antrr
    @36
    @33
    @43
    @27
    @2
    @18
    cA
    cB
    @49
    co
    wbr
    #
    wph
    @43
    @27
    @50
    wi
    wi
    @32
    wph
    @43
    @27
    @50
    wph
    cA
    cB
    cC
    @2
    @18
    initoeu1.c
    initoeu1.a
    initoeu1.b
    2initoinv
    3exp
    adantr
    imp31
    inviso1
    ex
    eximdv
    expcom
    exlimiv
    com3l
    impd
    syl2and
    imp
    @33
    @28
    @23
    simprl
    vf
    @11
    @26
    euelss
    syl3anc
    exp42
    com24
    com14
    expd
    syldc
    com15
    impd
    mpd
    impd
    mpd
end

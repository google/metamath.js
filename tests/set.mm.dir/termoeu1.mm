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
include "ctermo.mm"
include "eqid.mm"
include "istermoi.mm"
include "mpdan.mm"
include "wi.mm"
include "wceq.mm"
include "oveq1.mm"
include "eleq2d.mm"
include "eubidv.mm"
include "rspcv.mm"
include "wss.mm"
include "wex.mm"
include "ccat.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
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
include "2termoinv.mm"
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

theorem termoeu1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let va: setvar a
  let vg: setvar g
  let vb: setvar b
  assume termoeu1.c: |- ( ph -> C e. Cat )
  assume termoeu1.a: |- ( ph -> A e. ( TermO ` C ) )
  assume termoeu1.b: |- ( ph -> B e. ( TermO ` C ) )

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
  disjoint b g
  assert |- ( ph -> E! f f e. ( A ( Iso ` C ) B ) )

  proof
    wph
    cB
    cC
    cbs
    cfv
    #
    wcel
    #
    vf
    cv
    #
    va
    cv
    #
    cB
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
    va
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
    cB
    cC
    ctermo
    cfv
    #
    wcel
    @9
    termoeu1.b
    wph
    @0
    cC
    vf
    @4
    cB
    va
    @0
    eqid
    #
    @4
    eqid
    #
    termoeu1.c
    istermoi
    mpdan
    wph
    @1
    @8
    @13
    wph
    cA
    @0
    wcel
    #
    vg
    cv
    #
    vb
    cv
    #
    cA
    @4
    co
    #
    wcel
    #
    vg
    weu
    #
    vb
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
    cA
    @14
    wcel
    @24
    termoeu1.a
    wph
    @0
    cC
    vg
    @4
    cA
    vb
    @15
    @16
    termoeu1.c
    istermoi
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
    va
    cA
    @0
    @3
    cA
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
    cA
    cB
    @4
    oveq1
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
    termoeu1.c
    adantr
    #
    wph
    @17
    @1
    simprl
    #
    wph
    @17
    @1
    simprr
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
    vb
    cB
    @0
    @19
    cB
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
    cB
    cA
    @4
    oveq1
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
    @17
    @43
    @27
    @39
    ad2antrr
    @33
    @1
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
    termoeu1.c
    termoeu1.a
    termoeu1.b
    2termoinv
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

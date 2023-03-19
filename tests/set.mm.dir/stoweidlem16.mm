include "cv.mm"
include "wcel.mm"
include "w3a.mm"
include "cc0.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "wa.mm"
include "wral.mm"
include "crab.mm"
include "cmul.mm"
include "co.mm"
include "cmpt.mm"
include "simp1.mm"
include "weq.mm"
include "fveq1.mm"
include "breq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "elrab2.mm"
include "simplbi.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "syl3anc.mm"
include "syl5eqel.mm"
include "nfra1.mm"
include "nfcv.mm"
include "nfrab.mm"
include "nfcxfr.mm"
include "nfcri.mm"
include "nf3an.mm"
include "cr.mm"
include "wf.mm"
include "jca.mm"
include "adantr.mm"
include "syl.mm"
include "simpr.mm"
include "ffvelrnd.mm"
include "wi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "feq1.mm"
include "imbi12d.mm"
include "vtoclg.mm"
include "sylc.mm"
include "ffvelrnda.mm"
include "simprbi.mm"
include "r19.21bi.mm"
include "simpld.mm"
include "mulge0d.mm"
include "wceq.mm"
include "remulcld.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "breqtrrd.mm"
include "1red.mm"
include "simprd.mm"
include "lemul12ad.mm"
include "1t1e1.mm"
include "syl6breq.mm"
include "eqbrtrd.mm"
include "ex.mm"
include "ralrimi.mm"
include "nfmpt1.mm"
include "nfeq2.mm"
include "ralbid.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "syl6eleqr.mm"

theorem stoweidlem16
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cH: class H
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  assume stoweidlem16.1: |- F/ t ph
  assume stoweidlem16.2: |- Y = { h e. A | A. t e. T ( 0 <_ ( h ` t ) /\ ( h ` t ) <_ 1 ) }
  assume stoweidlem16.3: |- H = ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) )
  assume stoweidlem16.4: |- ( ( ph /\ f e. A ) -> f : T --> RR )
  assume stoweidlem16.5: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. A )

  disjoint f g
  disjoint f h
  disjoint f t
  disjoint A f
  disjoint g h
  disjoint g t
  disjoint A g
  disjoint h t
  disjoint A h
  disjoint A t
  disjoint T f
  disjoint T h
  disjoint T t
  disjoint f ph
  disjoint H h
  disjoint k x
  assert |- ( ( ph /\ f e. Y /\ g e. Y ) -> H e. Y )

  proof
    wph
    vf
    cv
    #
    cY
    wcel
    #
    vg
    cv
    #
    cY
    wcel
    #
    w3a
    #
    cH
    cc0
    vt
    cv
    #
    vh
    cv
    #
    cfv
    #
    cle
    wbr
    #
    @7
    c1
    cle
    wbr
    #
    wa
    #
    vt
    cT
    wral
    #
    vh
    cA
    crab
    #
    cY
    @4
    cH
    cA
    wcel
    cc0
    @5
    cH
    cfv
    #
    cle
    wbr
    #
    @13
    c1
    cle
    wbr
    #
    wa
    #
    vt
    cT
    wral
    #
    cH
    @12
    wcel
    @4
    cH
    vt
    cT
    @5
    @0
    cfv
    #
    @5
    @2
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    cA
    stoweidlem16.3
    @4
    wph
    @0
    cA
    wcel
    #
    @2
    cA
    wcel
    #
    @21
    cA
    wcel
    wph
    @1
    @3
    simp1
    #
    @1
    wph
    @22
    @3
    @1
    @22
    cc0
    @18
    cle
    wbr
    #
    @18
    c1
    cle
    wbr
    #
    wa
    #
    vt
    cT
    wral
    #
    @11
    @28
    vh
    @0
    cA
    cY
    vh
    vf
    weq
    #
    @10
    @27
    vt
    cT
    @29
    @8
    @25
    @9
    @26
    @29
    @7
    @18
    cc0
    cle
    @5
    @6
    @0
    fveq1
    #
    breq2d
    @29
    @7
    @18
    c1
    cle
    @30
    breq1d
    anbi12d
    ralbidv
    stoweidlem16.2
    elrab2
    #
    simplbi
    3ad2ant2
    #
    @3
    wph
    @23
    @1
    @3
    @23
    cc0
    @19
    cle
    wbr
    #
    @19
    c1
    cle
    wbr
    #
    wa
    #
    vt
    cT
    wral
    #
    @11
    @36
    vh
    @2
    cA
    cY
    vh
    vg
    weq
    #
    @10
    @35
    vt
    cT
    @37
    @8
    @33
    @9
    @34
    @37
    @7
    @19
    cc0
    cle
    @5
    @6
    @2
    fveq1
    #
    breq2d
    @37
    @7
    @19
    c1
    cle
    @38
    breq1d
    anbi12d
    ralbidv
    stoweidlem16.2
    elrab2
    #
    simplbi
    3ad2ant3
    #
    stoweidlem16.5
    syl3anc
    syl5eqel
    @4
    @16
    vt
    cT
    wph
    @1
    @3
    vt
    stoweidlem16.1
    vt
    vf
    cY
    vt
    cY
    @12
    stoweidlem16.2
    @11
    vt
    vh
    cA
    @10
    vt
    cT
    nfra1
    vt
    cA
    nfcv
    nfrab
    nfcxfr
    #
    nfcri
    vt
    vg
    cY
    @41
    nfcri
    nf3an
    @4
    @5
    cT
    wcel
    #
    @16
    @4
    @42
    wa
    #
    @14
    @15
    @43
    cc0
    @20
    @13
    cle
    @43
    @18
    @19
    @43
    cT
    cr
    @5
    @0
    @43
    wph
    @22
    wa
    #
    cT
    cr
    @0
    wf
    #
    @4
    @44
    @42
    @4
    wph
    @22
    @24
    @32
    jca
    adantr
    stoweidlem16.4
    syl
    @4
    @42
    simpr
    #
    ffvelrnd
    #
    @4
    cT
    cr
    @5
    @2
    @4
    @23
    wph
    @23
    wa
    #
    cT
    cr
    @2
    wf
    #
    @40
    @4
    wph
    @23
    @24
    @40
    jca
    @44
    @45
    wi
    @48
    @49
    wi
    vf
    @2
    cA
    vf
    vg
    weq
    #
    @44
    @48
    @45
    @49
    @50
    @22
    @23
    wph
    @0
    @2
    cA
    eleq1
    anbi2d
    cT
    cr
    @0
    @2
    feq1
    imbi12d
    stoweidlem16.4
    vtoclg
    sylc
    ffvelrnda
    #
    @43
    @25
    @26
    @4
    @27
    vt
    cT
    @1
    wph
    @28
    @3
    @1
    @22
    @28
    @31
    simprbi
    3ad2ant2
    r19.21bi
    #
    simpld
    #
    @43
    @33
    @34
    @4
    @35
    vt
    cT
    @3
    wph
    @36
    @1
    @3
    @23
    @36
    @39
    simprbi
    3ad2ant3
    r19.21bi
    #
    simpld
    #
    mulge0d
    @43
    @42
    @20
    cr
    wcel
    @13
    @20
    wceq
    @46
    @43
    @18
    @19
    @47
    @51
    remulcld
    vt
    cT
    @20
    cr
    cH
    stoweidlem16.3
    fvmpt2
    syl2anc
    #
    breqtrrd
    @43
    @13
    @20
    c1
    cle
    @56
    @43
    @20
    c1
    c1
    cmul
    co
    c1
    cle
    @43
    @18
    c1
    @19
    c1
    @47
    @43
    1red
    #
    @51
    @57
    @53
    @55
    @43
    @25
    @26
    @52
    simprd
    @43
    @33
    @34
    @54
    simprd
    lemul12ad
    1t1e1
    syl6breq
    eqbrtrd
    jca
    ex
    ralrimi
    @11
    @17
    vh
    cH
    cA
    @6
    cH
    wceq
    #
    @10
    @16
    vt
    cT
    vt
    @6
    cH
    vt
    cH
    @21
    stoweidlem16.3
    vt
    cT
    @20
    nfmpt1
    nfcxfr
    nfeq2
    @58
    @8
    @14
    @9
    @15
    @58
    @7
    @13
    cc0
    cle
    @5
    @6
    cH
    fveq1
    #
    breq2d
    @58
    @7
    @13
    c1
    cle
    @59
    breq1d
    anbi12d
    ralbid
    elrab
    sylanbrc
    stoweidlem16.2
    syl6eleqr
end

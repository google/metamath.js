include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "chom.mm"
include "co.mm"
include "cop.mm"
include "cco.mm"
include "cmpt.mm"
include "ccnv.mm"
include "wfun.mm"
include "wral.mm"
include "crab.mm"
include "cmpt2.mm"
include "cmon.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "eqid.mm"
include "chomf.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "simp-4r.mm"
include "homfeqval.mm"
include "ad5antr.mm"
include "ccomf.mm"
include "simplr.mm"
include "simp-5r.mm"
include "simpllr.mm"
include "comfeqval.mm"
include "mpteq12dva.mm"
include "cnveqd.mm"
include "funeqd.mm"
include "ralbidva.mm"
include "rabbidva.mm"
include "homfeqbas.mm"
include "raleqdv.mm"
include "rabeqbidv.mm"
include "eqtrd.mm"
include "3impa.mm"
include "mpt2eq3dva.mm"
include "mpt2eq12.mm"
include "syl2anc.mm"
include "monfval.mm"
include "3eqtr4d.mm"

theorem monpropd
  let wph: wff ph
  let cC: class C
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  assume monpropd.3: |- ( ph -> ( Homf ` C ) = ( Homf ` D ) )
  assume monpropd.4: |- ( ph -> ( comf ` C ) = ( comf ` D ) )
  assume monpropd.c: |- ( ph -> C e. Cat )
  assume monpropd.d: |- ( ph -> D e. Cat )


  assert |- ( ph -> ( Mono ` C ) = ( Mono ` D ) )

  proof
    wph
    va
    vb
    cC
    cbs
    cfv
    #
    @0
    vg
    vc
    cv
    #
    va
    cv
    #
    cC
    chom
    cfv
    #
    co
    #
    vf
    cv
    #
    vg
    cv
    #
    @1
    @2
    cop
    #
    vb
    cv
    #
    cC
    cco
    cfv
    #
    co
    co
    #
    cmpt
    #
    ccnv
    #
    wfun
    #
    vc
    @0
    wral
    #
    vf
    @2
    @8
    @3
    co
    #
    crab
    #
    cmpt2
    #
    va
    vb
    cD
    cbs
    cfv
    #
    @18
    vg
    @1
    @2
    cD
    chom
    cfv
    #
    co
    #
    @5
    @6
    @7
    @8
    cD
    cco
    cfv
    #
    co
    co
    #
    cmpt
    #
    ccnv
    #
    wfun
    #
    vc
    @18
    wral
    #
    vf
    @2
    @8
    @19
    co
    #
    crab
    #
    cmpt2
    #
    cC
    cmon
    cfv
    #
    cD
    cmon
    cfv
    #
    wph
    @17
    va
    vb
    @0
    @0
    @28
    cmpt2
    #
    @29
    wph
    va
    vb
    @0
    @0
    @16
    @28
    wph
    @2
    @0
    wcel
    #
    @8
    @0
    wcel
    #
    @16
    @28
    wceq
    wph
    @33
    wa
    #
    @34
    wa
    #
    @16
    @25
    vc
    @0
    wral
    #
    vf
    @15
    crab
    @28
    @36
    @14
    @37
    vf
    @15
    @36
    @5
    @15
    wcel
    #
    wa
    #
    @13
    @25
    vc
    @0
    @39
    @1
    @0
    wcel
    #
    wa
    #
    @12
    @24
    @41
    @11
    @23
    @41
    vg
    @4
    @10
    @20
    @22
    @41
    @0
    cC
    cD
    @3
    @19
    @1
    @2
    @0
    eqid
    #
    @3
    eqid
    #
    @19
    eqid
    #
    @36
    cC
    chomf
    cfv
    cD
    chomf
    cfv
    wceq
    #
    @38
    @40
    wph
    @45
    @33
    @34
    monpropd.3
    ad2antrr
    #
    ad2antrr
    @39
    @40
    simpr
    wph
    @33
    @34
    @38
    @40
    simp-4r
    homfeqval
    @41
    @6
    @4
    wcel
    #
    wa
    @0
    cC
    cD
    @21
    @9
    @6
    @5
    @3
    @1
    @2
    @8
    @42
    @43
    @9
    eqid
    #
    @21
    eqid
    #
    wph
    @45
    @33
    @34
    @38
    @40
    @47
    monpropd.3
    ad5antr
    wph
    cC
    ccomf
    cfv
    cD
    ccomf
    cfv
    wceq
    @33
    @34
    @38
    @40
    @47
    monpropd.4
    ad5antr
    @39
    @40
    @47
    simplr
    wph
    @33
    @34
    @38
    @40
    @47
    simp-5r
    @35
    @34
    @38
    @40
    @47
    simp-4r
    @41
    @47
    simpr
    @36
    @38
    @40
    @47
    simpllr
    comfeqval
    mpteq12dva
    cnveqd
    funeqd
    ralbidva
    rabbidva
    @36
    @37
    @26
    vf
    @15
    @27
    @36
    @0
    cC
    cD
    @3
    @19
    @2
    @8
    @42
    @43
    @44
    @46
    wph
    @33
    @34
    simplr
    @35
    @34
    simpr
    homfeqval
    @36
    @25
    vc
    @0
    @18
    wph
    @0
    @18
    wceq
    #
    @33
    @34
    wph
    cC
    cD
    monpropd.3
    homfeqbas
    #
    ad2antrr
    raleqdv
    rabeqbidv
    eqtrd
    3impa
    mpt2eq3dva
    wph
    @50
    @50
    @32
    @29
    wceq
    @51
    @51
    va
    vb
    @0
    @0
    @18
    @18
    @28
    mpt2eq12
    syl2anc
    eqtrd
    wph
    va
    vb
    vc
    @0
    cC
    @9
    vf
    vg
    @3
    @30
    @42
    @43
    @48
    @30
    eqid
    monpropd.c
    monfval
    wph
    va
    vb
    vc
    @18
    cD
    @21
    vf
    vg
    @19
    @31
    @18
    eqid
    @44
    @49
    @31
    eqid
    monpropd.d
    monfval
    3eqtr4d
end

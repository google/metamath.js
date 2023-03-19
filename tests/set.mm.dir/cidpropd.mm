include "ccat.mm"
include "wcel.mm"
include "ccid.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cbs.mm"
include "cv.mm"
include "cop.mm"
include "cco.mm"
include "co.mm"
include "chom.mm"
include "wral.mm"
include "crio.mm"
include "cmpt.mm"
include "homfeqbas.mm"
include "adantr.mm"
include "eqid.mm"
include "chomf.mm"
include "ad4antr.mm"
include "simpr.mm"
include "simpllr.mm"
include "homfeqval.mm"
include "ad5antr.mm"
include "ccomf.mm"
include "simplr.mm"
include "simp-4r.mm"
include "comfeqval.mm"
include "eqeq1d.mm"
include "raleqbidva.mm"
include "anbi12d.mm"
include "ralbidva.mm"
include "riotabidva.mm"
include "ad2antrr.mm"
include "raleqdv.mm"
include "riotaeqbidv.mm"
include "eqtrd.mm"
include "mpteq12dva.mm"
include "cidfval.mm"
include "catpropd.mm"
include "biimpa.mm"
include "3eqtr4d.mm"
include "wn.mm"
include "c0.mm"
include "cdm.mm"
include "wfn.mm"
include "cidffn.mm"
include "fndm.mm"
include "ax-mp.mm"
include "eleq2i.mm"
include "sylnibr.mm"
include "ndmfv.mm"
include "syl.mm"
include "syl6bbr.mm"
include "notbid.mm"
include "eqtr4d.mm"
include "pm2.61dan.mm"

theorem cidpropd
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume catpropd.1: |- ( ph -> ( Homf ` C ) = ( Homf ` D ) )
  assume catpropd.2: |- ( ph -> ( comf ` C ) = ( comf ` D ) )
  assume catpropd.3: |- ( ph -> C e. V )
  assume catpropd.4: |- ( ph -> D e. W )


  assert |- ( ph -> ( Id ` C ) = ( Id ` D ) )

  proof
    wph
    cC
    ccat
    wcel
    #
    cC
    ccid
    cfv
    #
    cD
    ccid
    cfv
    #
    wceq
    wph
    @0
    wa
    #
    vx
    cC
    cbs
    cfv
    #
    vg
    cv
    #
    vf
    cv
    #
    vy
    cv
    #
    vx
    cv
    #
    cop
    #
    @8
    cC
    cco
    cfv
    #
    co
    co
    #
    @6
    wceq
    #
    vf
    @7
    @8
    cC
    chom
    cfv
    #
    co
    #
    wral
    #
    @6
    @5
    @8
    @8
    cop
    #
    @7
    @10
    co
    co
    #
    @6
    wceq
    #
    vf
    @8
    @7
    @13
    co
    #
    wral
    #
    wa
    #
    vy
    @4
    wral
    #
    vg
    @8
    @8
    @13
    co
    #
    crio
    #
    cmpt
    vx
    cD
    cbs
    cfv
    #
    @5
    @6
    @9
    @8
    cD
    cco
    cfv
    #
    co
    co
    #
    @6
    wceq
    #
    vf
    @7
    @8
    cD
    chom
    cfv
    #
    co
    #
    wral
    #
    @6
    @5
    @16
    @7
    @26
    co
    co
    #
    @6
    wceq
    #
    vf
    @8
    @7
    @29
    co
    #
    wral
    #
    wa
    #
    vy
    @25
    wral
    #
    vg
    @8
    @8
    @29
    co
    #
    crio
    #
    cmpt
    @1
    @2
    @3
    vx
    @4
    @24
    @25
    @39
    wph
    @4
    @25
    wceq
    #
    @0
    wph
    cC
    cD
    catpropd.1
    homfeqbas
    #
    adantr
    @3
    @8
    @4
    wcel
    #
    wa
    #
    @24
    @36
    vy
    @4
    wral
    #
    vg
    @23
    crio
    @39
    @43
    @22
    @44
    vg
    @23
    @43
    @5
    @23
    wcel
    #
    wa
    #
    @21
    @36
    vy
    @4
    @46
    @7
    @4
    wcel
    #
    wa
    #
    @15
    @31
    @20
    @35
    @48
    @12
    @28
    vf
    @14
    @30
    @48
    @4
    cC
    cD
    @13
    @29
    @7
    @8
    @4
    eqid
    #
    @13
    eqid
    #
    @29
    eqid
    #
    wph
    cC
    chomf
    cfv
    cD
    chomf
    cfv
    wceq
    #
    @0
    @42
    @45
    @47
    catpropd.1
    ad4antr
    #
    @46
    @47
    simpr
    #
    @3
    @42
    @45
    @47
    simpllr
    #
    homfeqval
    @48
    @6
    @14
    wcel
    #
    wa
    #
    @11
    @27
    @6
    @57
    @4
    cC
    cD
    @26
    @10
    @6
    @5
    @13
    @7
    @8
    @8
    @49
    @50
    @10
    eqid
    #
    @26
    eqid
    #
    wph
    @52
    @0
    @42
    @45
    @47
    @56
    catpropd.1
    ad5antr
    wph
    cC
    ccomf
    cfv
    cD
    ccomf
    cfv
    wceq
    #
    @0
    @42
    @45
    @47
    @56
    catpropd.2
    ad5antr
    @46
    @47
    @56
    simplr
    @3
    @42
    @45
    @47
    @56
    simp-4r
    #
    @61
    @48
    @56
    simpr
    @43
    @45
    @47
    @56
    simpllr
    comfeqval
    eqeq1d
    raleqbidva
    @48
    @18
    @33
    vf
    @19
    @34
    @48
    @4
    cC
    cD
    @13
    @29
    @8
    @7
    @49
    @50
    @51
    @53
    @55
    @54
    homfeqval
    @48
    @6
    @19
    wcel
    #
    wa
    #
    @17
    @32
    @6
    @63
    @4
    cC
    cD
    @26
    @10
    @5
    @6
    @13
    @8
    @8
    @7
    @49
    @50
    @58
    @59
    @48
    @52
    @62
    @53
    adantr
    wph
    @60
    @0
    @42
    @45
    @47
    @62
    catpropd.2
    ad5antr
    @48
    @42
    @62
    @55
    adantr
    #
    @64
    @46
    @47
    @62
    simplr
    @43
    @45
    @47
    @62
    simpllr
    @48
    @62
    simpr
    comfeqval
    eqeq1d
    raleqbidva
    anbi12d
    ralbidva
    riotabidva
    @43
    @44
    @37
    vg
    @23
    @38
    @43
    @4
    cC
    cD
    @13
    @29
    @8
    @8
    @49
    @50
    @51
    wph
    @52
    @0
    @42
    catpropd.1
    ad2antrr
    @3
    @42
    simpr
    #
    @65
    homfeqval
    @43
    @36
    vy
    @4
    @25
    wph
    @40
    @0
    @42
    @41
    ad2antrr
    raleqdv
    riotaeqbidv
    eqtrd
    mpteq12dva
    @3
    vx
    vy
    @4
    cC
    @10
    @1
    vf
    vg
    @13
    @49
    @50
    @58
    wph
    @0
    simpr
    @1
    eqid
    cidfval
    @3
    vx
    vy
    @25
    cD
    @26
    @2
    vf
    vg
    @29
    @25
    eqid
    @51
    @59
    wph
    @0
    cD
    ccat
    wcel
    #
    wph
    cC
    cD
    cV
    cW
    catpropd.1
    catpropd.2
    catpropd.3
    catpropd.4
    catpropd
    #
    biimpa
    @2
    eqid
    cidfval
    3eqtr4d
    wph
    @0
    wn
    #
    wa
    #
    @1
    c0
    @2
    @69
    cC
    ccid
    cdm
    #
    wcel
    #
    wn
    @1
    c0
    wceq
    @69
    @0
    @71
    wph
    @68
    simpr
    @70
    ccat
    cC
    ccid
    ccat
    wfn
    @70
    ccat
    wceq
    cidffn
    ccat
    ccid
    fndm
    ax-mp
    #
    eleq2i
    sylnibr
    cC
    ccid
    ndmfv
    syl
    @69
    cD
    @70
    wcel
    #
    wn
    #
    @2
    c0
    wceq
    wph
    @68
    @74
    wph
    @0
    @73
    wph
    @0
    @66
    @73
    @67
    @70
    ccat
    cD
    @72
    eleq2i
    syl6bbr
    notbid
    biimpa
    cD
    ccid
    ndmfv
    syl
    eqtr4d
    pm2.61dan
end

include "cress.mm"
include "co.mm"
include "chomf.mm"
include "cfv.mm"
include "wceq.mm"
include "ccomf.mm"
include "cv.mm"
include "chom.mm"
include "ccat.mm"
include "cin.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cfunc.mm"
include "cbs.mm"
include "cvv.mm"
include "eqid.mm"
include "ssexd.mm"
include "adantr.mm"
include "simprl.mm"
include "catcbas.mm"
include "eleqtrrd.mm"
include "simprr.mm"
include "catchom.mm"
include "wss.mm"
include "ineq2d.mm"
include "inass.mm"
include "syl6reqr.mm"
include "df-ss.mm"
include "sylib.mm"
include "ineq1d.mm"
include "ressbas.mm"
include "syl.mm"
include "3eqtr3d.mm"
include "ressbasss.mm"
include "syl6eqss.mm"
include "sseldd.mm"
include "resshom.mm"
include "oveqdr.mm"
include "3eqtr2rd.mm"
include "ralrimivva.mm"
include "eqcomd.mm"
include "homfeq.mm"
include "mpbird.mm"
include "cop.mm"
include "cco.mm"
include "w3a.mm"
include "ccofu.mm"
include "ad2antrr.mm"
include "simplr1.mm"
include "simplr2.mm"
include "simplr3.mm"
include "eleqtrd.mm"
include "catcco.mm"
include "ressco.mm"
include "oveqd.mm"
include "3eqtr2d.mm"
include "ralrimivvva.mm"
include "comfeq.mm"
include "jca.mm"

theorem resscatc
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cU: class U
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume resscatc.c: |- C = ( CatCat ` U )
  assume resscatc.d: |- D = ( CatCat ` V )
  assume resscatc.1: |- ( ph -> U e. W )
  assume resscatc.2: |- ( ph -> V C_ U )


  assert |- ( ph -> ( ( Homf ` ( C |`s V ) ) = ( Homf ` D ) /\ ( comf ` ( C |`s V ) ) = ( comf ` D ) ) )

  proof
    wph
    cC
    cV
    cress
    co
    #
    chomf
    cfv
    #
    cD
    chomf
    cfv
    #
    wceq
    #
    @0
    ccomf
    cfv
    #
    cD
    ccomf
    cfv
    #
    wceq
    wph
    @3
    vx
    cv
    #
    vy
    cv
    #
    @0
    chom
    cfv
    #
    co
    #
    @6
    @7
    cD
    chom
    cfv
    #
    co
    #
    wceq
    #
    vy
    cV
    ccat
    cin
    #
    wral
    vx
    @13
    wral
    wph
    @12
    vx
    vy
    @13
    @13
    wph
    @6
    @13
    wcel
    #
    @7
    @13
    wcel
    #
    wa
    #
    wa
    #
    @11
    @6
    @7
    cfunc
    co
    #
    @6
    @7
    cC
    chom
    cfv
    #
    co
    @9
    @17
    cD
    cbs
    cfv
    #
    cD
    cV
    @10
    cvv
    @6
    @7
    resscatc.d
    @20
    eqid
    #
    wph
    cV
    cvv
    wcel
    #
    @16
    wph
    cV
    cU
    cW
    resscatc.1
    resscatc.2
    ssexd
    #
    adantr
    @10
    eqid
    #
    @17
    @6
    @13
    @20
    wph
    @14
    @15
    simprl
    #
    wph
    @20
    @13
    wceq
    #
    @16
    wph
    @20
    cD
    cV
    cvv
    resscatc.d
    @21
    @23
    catcbas
    #
    adantr
    #
    eleqtrrd
    @17
    @7
    @13
    @20
    wph
    @14
    @15
    simprr
    #
    @28
    eleqtrrd
    catchom
    @17
    cC
    cbs
    cfv
    #
    cC
    cU
    @19
    cW
    @6
    @7
    resscatc.c
    @30
    eqid
    #
    wph
    cU
    cW
    wcel
    #
    @16
    resscatc.1
    adantr
    @19
    eqid
    #
    @17
    @13
    @30
    @6
    wph
    @13
    @30
    wss
    #
    @16
    wph
    @13
    @0
    cbs
    cfv
    #
    @30
    wph
    cV
    cU
    cin
    #
    ccat
    cin
    #
    cV
    @30
    cin
    #
    @13
    @35
    wph
    @38
    cV
    cU
    ccat
    cin
    #
    cin
    @37
    wph
    @30
    @39
    cV
    wph
    @30
    cC
    cU
    cW
    resscatc.c
    @31
    resscatc.1
    catcbas
    ineq2d
    cV
    cU
    ccat
    inass
    syl6reqr
    wph
    @36
    cV
    ccat
    wph
    cV
    cU
    wss
    @36
    cV
    wceq
    resscatc.2
    cV
    cU
    df-ss
    sylib
    ineq1d
    wph
    @22
    @38
    @35
    wceq
    @23
    cV
    @30
    @0
    cvv
    cC
    @0
    eqid
    #
    @31
    ressbas
    syl
    3eqtr3d
    #
    cV
    @30
    @0
    cC
    @40
    @31
    ressbasss
    syl6eqss
    #
    adantr
    #
    @25
    sseldd
    @17
    @13
    @30
    @7
    @43
    @29
    sseldd
    catchom
    wph
    @16
    vx
    vy
    @19
    @8
    wph
    @22
    @19
    @8
    wceq
    @23
    cV
    cC
    @0
    @19
    cvv
    @40
    @33
    resshom
    syl
    oveqdr
    3eqtr2rd
    ralrimivva
    wph
    vx
    vy
    @13
    @0
    cD
    @8
    @10
    @8
    eqid
    @24
    @41
    wph
    @20
    @13
    @27
    eqcomd
    #
    homfeq
    mpbird
    #
    wph
    @5
    @4
    wph
    @5
    @4
    wceq
    vg
    cv
    #
    vf
    cv
    #
    @6
    @7
    cop
    #
    vz
    cv
    #
    cD
    cco
    cfv
    #
    co
    co
    #
    @46
    @47
    @48
    @49
    @0
    cco
    cfv
    #
    co
    #
    co
    #
    wceq
    #
    vg
    @7
    @49
    @10
    co
    #
    wral
    vf
    @11
    wral
    #
    vz
    @13
    wral
    vy
    @13
    wral
    vx
    @13
    wral
    wph
    @57
    vx
    vy
    vz
    @13
    @13
    @13
    wph
    @14
    @15
    @49
    @13
    wcel
    #
    w3a
    #
    wa
    #
    @55
    vf
    vg
    @11
    @56
    @60
    @47
    @11
    wcel
    #
    @46
    @56
    wcel
    #
    wa
    #
    wa
    #
    @51
    @46
    @47
    ccofu
    co
    @46
    @47
    @48
    @49
    cC
    cco
    cfv
    #
    co
    #
    co
    @54
    @64
    @20
    cD
    @50
    cV
    @47
    @46
    cvv
    @6
    @7
    @49
    resscatc.d
    @21
    wph
    @22
    @59
    @63
    @23
    ad2antrr
    #
    @50
    eqid
    #
    @64
    @6
    @13
    @20
    @14
    @15
    @58
    wph
    @63
    simplr1
    #
    wph
    @26
    @59
    @63
    @27
    ad2antrr
    #
    eleqtrrd
    #
    @64
    @7
    @13
    @20
    @14
    @15
    @58
    wph
    @63
    simplr2
    #
    @70
    eleqtrrd
    #
    @64
    @49
    @13
    @20
    @14
    @15
    @58
    wph
    @63
    simplr3
    #
    @70
    eleqtrrd
    #
    @64
    @47
    @11
    @18
    @60
    @61
    @62
    simprl
    @64
    @20
    cD
    cV
    @10
    cvv
    @6
    @7
    resscatc.d
    @21
    @67
    @24
    @71
    @73
    catchom
    eleqtrd
    #
    @64
    @46
    @56
    @7
    @49
    cfunc
    co
    @60
    @61
    @62
    simprr
    @64
    @20
    cD
    cV
    @10
    cvv
    @7
    @49
    resscatc.d
    @21
    @67
    @24
    @73
    @75
    catchom
    eleqtrd
    #
    catcco
    @64
    @30
    cC
    @65
    cU
    @47
    @46
    cW
    @6
    @7
    @49
    resscatc.c
    @31
    wph
    @32
    @59
    @63
    resscatc.1
    ad2antrr
    @65
    eqid
    #
    @64
    @13
    @30
    @6
    wph
    @34
    @59
    @63
    @42
    ad2antrr
    #
    @69
    sseldd
    @64
    @13
    @30
    @7
    @79
    @72
    sseldd
    @64
    @13
    @30
    @49
    @79
    @74
    sseldd
    @76
    @77
    catcco
    @64
    @66
    @53
    @46
    @47
    @64
    @65
    @52
    @48
    @49
    wph
    @65
    @52
    wceq
    #
    @59
    @63
    wph
    @22
    @80
    @23
    cV
    cC
    @0
    @65
    cvv
    @40
    @78
    ressco
    syl
    ad2antrr
    oveqd
    oveqd
    3eqtr2d
    ralrimivva
    ralrimivvva
    wph
    vx
    vy
    vz
    @13
    cD
    @0
    @52
    @50
    vf
    vg
    @10
    @68
    @52
    eqid
    @24
    @44
    @41
    wph
    @1
    @2
    @45
    eqcomd
    comfeq
    mpbird
    eqcomd
    jca
end

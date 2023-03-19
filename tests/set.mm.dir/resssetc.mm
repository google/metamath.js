include "cress.mm"
include "co.mm"
include "chomf.mm"
include "cfv.mm"
include "wceq.mm"
include "ccomf.mm"
include "cv.mm"
include "chom.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cmap.mm"
include "cvv.mm"
include "ssexd.mm"
include "adantr.mm"
include "eqid.mm"
include "simprl.mm"
include "simprr.mm"
include "setchom.mm"
include "wss.mm"
include "sseldd.mm"
include "resshom.mm"
include "syl.mm"
include "oveqdr.mm"
include "3eqtr2rd.mm"
include "ralrimivva.mm"
include "cbs.mm"
include "setcbas.mm"
include "sseqtrd.mm"
include "ressbas2.mm"
include "homfeq.mm"
include "mpbird.mm"
include "cop.mm"
include "cco.mm"
include "w3a.mm"
include "ccom.mm"
include "ad2antrr.mm"
include "simplr1.mm"
include "simplr2.mm"
include "simplr3.mm"
include "wf.mm"
include "elsetchom.mm"
include "mpbid.mm"
include "setcco.mm"
include "ressco.mm"
include "oveqd.mm"
include "3eqtr2d.mm"
include "ralrimivvva.mm"
include "eqcomd.mm"
include "comfeq.mm"
include "jca.mm"

theorem resssetc
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
  let cE: class E
  assume resssetc.c: |- C = ( SetCat ` U )
  assume resssetc.d: |- D = ( SetCat ` V )
  assume resssetc.1: |- ( ph -> U e. W )
  assume resssetc.2: |- ( ph -> V C_ U )


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
    wral
    vx
    cV
    wral
    wph
    @12
    vx
    vy
    cV
    cV
    wph
    @6
    cV
    wcel
    #
    @7
    cV
    wcel
    #
    wa
    #
    wa
    #
    @11
    @7
    @6
    cmap
    co
    @6
    @7
    cC
    chom
    cfv
    #
    co
    @9
    @16
    cD
    cV
    @10
    cvv
    @6
    @7
    resssetc.d
    wph
    cV
    cvv
    wcel
    #
    @15
    wph
    cV
    cU
    cW
    resssetc.1
    resssetc.2
    ssexd
    #
    adantr
    @10
    eqid
    #
    wph
    @13
    @14
    simprl
    #
    wph
    @13
    @14
    simprr
    #
    setchom
    @16
    cC
    cU
    @17
    cW
    @6
    @7
    resssetc.c
    wph
    cU
    cW
    wcel
    #
    @15
    resssetc.1
    adantr
    @17
    eqid
    #
    @16
    cV
    cU
    @6
    wph
    cV
    cU
    wss
    #
    @15
    resssetc.2
    adantr
    #
    @21
    sseldd
    @16
    cV
    cU
    @7
    @26
    @22
    sseldd
    setchom
    wph
    @15
    vx
    vy
    @17
    @8
    wph
    @18
    @17
    @8
    wceq
    @19
    cV
    cC
    @0
    @17
    cvv
    @0
    eqid
    #
    @24
    resshom
    syl
    oveqdr
    3eqtr2rd
    ralrimivva
    wph
    vx
    vy
    cV
    @0
    cD
    @8
    @10
    @8
    eqid
    @20
    wph
    cV
    cC
    cbs
    cfv
    #
    wss
    cV
    @0
    cbs
    cfv
    wceq
    wph
    cV
    cU
    @28
    resssetc.2
    wph
    cC
    cU
    cW
    resssetc.c
    resssetc.1
    setcbas
    sseqtrd
    cV
    @28
    @0
    cC
    @27
    @28
    eqid
    ressbas2
    syl
    #
    wph
    cD
    cV
    cvv
    resssetc.d
    @19
    setcbas
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
    @32
    @33
    @34
    @35
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
    @35
    @10
    co
    #
    wral
    vf
    @11
    wral
    #
    vz
    cV
    wral
    vy
    cV
    wral
    vx
    cV
    wral
    wph
    @43
    vx
    vy
    vz
    cV
    cV
    cV
    wph
    @13
    @14
    @35
    cV
    wcel
    #
    w3a
    #
    wa
    #
    @41
    vf
    vg
    @11
    @42
    @46
    @33
    @11
    wcel
    #
    @32
    @42
    wcel
    #
    wa
    #
    wa
    #
    @37
    @32
    @33
    ccom
    @32
    @33
    @34
    @35
    cC
    cco
    cfv
    #
    co
    #
    co
    @40
    @50
    cD
    @36
    cV
    @33
    @32
    cvv
    @6
    @7
    @35
    resssetc.d
    wph
    @18
    @45
    @49
    @19
    ad2antrr
    #
    @36
    eqid
    #
    @13
    @14
    @44
    wph
    @49
    simplr1
    #
    @13
    @14
    @44
    wph
    @49
    simplr2
    #
    @13
    @14
    @44
    wph
    @49
    simplr3
    #
    @50
    @47
    @6
    @7
    @33
    wf
    @46
    @47
    @48
    simprl
    @50
    cD
    cV
    @33
    @10
    cvv
    @6
    @7
    resssetc.d
    @53
    @20
    @55
    @56
    elsetchom
    mpbid
    #
    @50
    @48
    @7
    @35
    @32
    wf
    @46
    @47
    @48
    simprr
    @50
    cD
    cV
    @32
    @10
    cvv
    @7
    @35
    resssetc.d
    @53
    @20
    @56
    @57
    elsetchom
    mpbid
    #
    setcco
    @50
    cC
    @51
    cU
    @33
    @32
    cW
    @6
    @7
    @35
    resssetc.c
    wph
    @23
    @45
    @49
    resssetc.1
    ad2antrr
    @51
    eqid
    #
    @50
    cV
    cU
    @6
    wph
    @25
    @45
    @49
    resssetc.2
    ad2antrr
    #
    @55
    sseldd
    @50
    cV
    cU
    @7
    @61
    @56
    sseldd
    @50
    cV
    cU
    @35
    @61
    @57
    sseldd
    @58
    @59
    setcco
    @50
    @52
    @39
    @32
    @33
    @50
    @51
    @38
    @34
    @35
    wph
    @51
    @38
    wceq
    #
    @45
    @49
    wph
    @18
    @62
    @19
    cV
    cC
    @0
    @51
    cvv
    @27
    @60
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
    cV
    cD
    @0
    @38
    @36
    vf
    vg
    @10
    @54
    @38
    eqid
    @20
    @30
    @29
    wph
    @1
    @2
    @31
    eqcomd
    comfeq
    mpbird
    eqcomd
    jca
end

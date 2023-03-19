include "cres.mm"
include "caddc.mm"
include "co.mm"
include "climc.mm"
include "wcel.mm"
include "cc.mm"
include "cv.mm"
include "wne.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "limccl.mm"
include "sseldi.mm"
include "cdm.mm"
include "fssresd.mm"
include "wf.mm"
include "wss.mm"
include "w3a.mm"
include "limcrcl.mm"
include "syl.mm"
include "simp3d.mm"
include "ellimc3.mm"
include "mpbid.mm"
include "simprd.mm"
include "r19.21bi.mm"
include "wceq.mm"
include "simpl1l.mm"
include "adantr.mm"
include "simplr.mm"
include "crab.mm"
include "id.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "syl5bb.mm"
include "cbvrabv.mm"
include "eqtri.mm"
include "syl6eleq.mm"
include "elrab.mm"
include "sylib.mm"
include "adantl.mm"
include "3ad2ant3.mm"
include "sselda.mm"
include "pncand.mm"
include "3adant3.mm"
include "eqtrd.mm"
include "simp2.mm"
include "eqeltrd.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "a1i.mm"
include "npcand.mm"
include "eqcomd.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "nfv.mm"
include "nfrab1.mm"
include "nfcxfr.mm"
include "nfcri.mm"
include "nfan.mm"
include "nfcv.mm"
include "nfres.mm"
include "nffv.mm"
include "nfov.mm"
include "nfbr.mm"
include "simp3.mm"
include "fveq2d.mm"
include "3ad2ant1.mm"
include "eqeltrrd.mm"
include "fvres.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "chvarv.mm"
include "eqtr4d.mm"
include "3eqtrd.mm"
include "oveq1d.mm"
include "simpll3.mm"
include "jca.mm"
include "simp1rl.mm"
include "neneqd.mm"
include "sylan9eq.mm"
include "mtand.mm"
include "neqned.mm"
include "pnpcan2d.mm"
include "eqtr2d.mm"
include "simp1rr.mm"
include "eqbrtrd.mm"
include "neeq1.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "rspccva.mm"
include "sylc.mm"
include "rexlimd.mm"
include "ex.mm"
include "ralrimiva.mm"
include "reximdvai.mm"
include "addcld.mm"
include "mpbir2and.mm"

theorem limcperiod
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  let cF: class F
  let vb: setvar b
  let vw: setvar w
  let vz: setvar z
  assume limcperiod.f: |- ( ph -> F : dom F --> CC )
  assume limcperiod.assc: |- ( ph -> A C_ CC )
  assume limcperiod.3: |- ( ph -> A C_ dom F )
  assume limcperiod.t: |- ( ph -> T e. CC )
  assume limcperiod.b: |- B = { x e. CC | E. y e. A x = ( y + T ) }
  assume limcperiod.bss: |- ( ph -> B C_ dom F )
  assume limcperiod.fper: |- ( ( ph /\ y e. A ) -> ( F ` ( y + T ) ) = ( F ` y ) )
  assume limcperiod.clim: |- ( ph -> C e. ( ( F |` A ) limCC D ) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint F x
  disjoint F y
  disjoint T x
  disjoint T y
  disjoint ph x
  disjoint ph y
  disjoint A b
  disjoint A w
  disjoint A z
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint B b
  disjoint B w
  disjoint B z
  disjoint C b
  disjoint C w
  disjoint C z
  disjoint D b
  disjoint D w
  disjoint D z
  disjoint F b
  disjoint F w
  disjoint F z
  disjoint T b
  disjoint T w
  disjoint T z
  disjoint b ph
  disjoint ph w
  disjoint ph z
  assert |- ( ph -> C e. ( ( F |` B ) limCC ( D + T ) ) )

  proof
    wph
    cC
    cF
    cB
    cres
    #
    cD
    cT
    caddc
    co
    #
    climc
    co
    wcel
    cC
    cc
    wcel
    #
    vb
    cv
    #
    @1
    wne
    #
    @3
    @1
    cmin
    co
    #
    cabs
    cfv
    #
    vz
    cv
    #
    clt
    wbr
    #
    wa
    #
    @3
    @0
    cfv
    #
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    vw
    cv
    #
    clt
    wbr
    #
    wi
    #
    vb
    cB
    wral
    #
    vz
    crp
    wrex
    #
    vw
    crp
    wral
    wph
    cF
    cA
    cres
    #
    cD
    climc
    co
    #
    cc
    cC
    cD
    @18
    limccl
    limcperiod.clim
    sseldi
    wph
    @17
    vw
    crp
    wph
    @13
    crp
    wcel
    #
    wa
    #
    vy
    cv
    #
    cD
    wne
    #
    @22
    cD
    cmin
    co
    #
    cabs
    cfv
    #
    @7
    clt
    wbr
    #
    wa
    #
    @22
    @18
    cfv
    #
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    @13
    clt
    wbr
    #
    wi
    #
    vy
    cA
    wral
    #
    vz
    crp
    wrex
    #
    @17
    wph
    @34
    vw
    crp
    wph
    @2
    @34
    vw
    crp
    wral
    #
    wph
    cC
    @19
    wcel
    #
    @2
    @35
    wa
    limcperiod.clim
    wph
    vw
    vz
    vy
    cA
    cD
    cC
    @18
    wph
    cF
    cdm
    #
    cc
    cA
    cF
    limcperiod.f
    limcperiod.3
    fssresd
    limcperiod.assc
    wph
    @18
    cdm
    #
    cc
    @18
    wf
    #
    @38
    cc
    wss
    #
    cD
    cc
    wcel
    #
    wph
    @36
    @39
    @40
    @41
    w3a
    limcperiod.clim
    cD
    cC
    @18
    limcrcl
    syl
    simp3d
    #
    ellimc3
    mpbid
    simprd
    r19.21bi
    @21
    @33
    @16
    vz
    crp
    @21
    @7
    crp
    wcel
    #
    @33
    @16
    @21
    @43
    @33
    w3a
    #
    @15
    vb
    cB
    @44
    @3
    cB
    wcel
    #
    wa
    #
    @9
    @14
    @46
    @9
    wa
    #
    @3
    vx
    cv
    #
    cT
    caddc
    co
    #
    wceq
    #
    vx
    cA
    wrex
    #
    @14
    @47
    wph
    @45
    @51
    @46
    wph
    @9
    wph
    @20
    @43
    @33
    @45
    simpl1l
    adantr
    #
    @44
    @45
    @9
    simplr
    #
    wph
    @45
    wa
    #
    @3
    cT
    cmin
    co
    #
    cA
    wcel
    #
    @3
    @55
    cT
    caddc
    co
    #
    wceq
    #
    @51
    @54
    @3
    @7
    cT
    caddc
    co
    #
    wceq
    #
    vz
    cA
    wrex
    #
    @56
    @45
    @61
    wph
    @45
    @3
    cc
    wcel
    #
    @61
    @45
    @3
    @13
    @59
    wceq
    #
    vz
    cA
    wrex
    #
    vw
    cc
    crab
    #
    wcel
    @62
    @61
    wa
    @45
    @3
    cB
    @65
    @45
    id
    cB
    @48
    @22
    cT
    caddc
    co
    #
    wceq
    #
    vy
    cA
    wrex
    #
    vx
    cc
    crab
    #
    @65
    limcperiod.b
    @68
    @64
    vx
    vw
    cc
    @68
    @48
    @59
    wceq
    #
    vz
    cA
    wrex
    @48
    @13
    wceq
    #
    @64
    @67
    @70
    vy
    vz
    cA
    @22
    @7
    wceq
    @66
    @59
    @48
    @22
    @7
    cT
    caddc
    oveq1
    eqeq2d
    cbvrexv
    @71
    @70
    @63
    vz
    cA
    @48
    @13
    @59
    eqeq1
    rexbidv
    syl5bb
    cbvrabv
    eqtri
    #
    syl6eleq
    @64
    @61
    vw
    @3
    cc
    @13
    @3
    wceq
    @63
    @60
    vz
    cA
    @13
    @3
    @59
    eqeq1
    rexbidv
    elrab
    sylib
    simprd
    adantl
    @54
    @60
    @56
    vz
    cA
    wph
    @7
    cA
    wcel
    #
    @60
    @56
    wi
    wi
    @45
    wph
    @73
    @60
    @56
    wph
    @73
    @60
    w3a
    #
    @55
    @7
    cA
    @74
    @55
    @59
    cT
    cmin
    co
    #
    @7
    @60
    wph
    @55
    @75
    wceq
    @73
    @3
    @59
    cT
    cmin
    oveq1
    3ad2ant3
    wph
    @73
    @75
    @7
    wceq
    @60
    wph
    @73
    wa
    @7
    cT
    wph
    cA
    cc
    @7
    limcperiod.assc
    sselda
    wph
    cT
    cc
    wcel
    #
    @73
    limcperiod.t
    adantr
    pncand
    3adant3
    eqtrd
    wph
    @73
    @60
    simp2
    eqeltrd
    3exp
    adantr
    rexlimdv
    mpd
    @54
    @57
    @3
    @54
    @3
    cT
    wph
    cB
    cc
    @3
    cB
    cc
    wss
    wph
    cB
    @65
    cc
    @72
    @64
    vw
    cc
    ssrab2
    eqsstri
    a1i
    #
    sselda
    wph
    @76
    @45
    limcperiod.t
    adantr
    npcand
    eqcomd
    @50
    @58
    vx
    @55
    cA
    @48
    @55
    wceq
    @49
    @57
    @3
    @48
    @55
    cT
    caddc
    oveq1
    eqeq2d
    rspcev
    syl2anc
    syl2anc
    @47
    @50
    @14
    vx
    cA
    @46
    @9
    vx
    @44
    @45
    vx
    @44
    vx
    nfv
    vx
    vb
    cB
    vx
    cB
    @69
    limcperiod.b
    @68
    vx
    cc
    nfrab1
    nfcxfr
    #
    nfcri
    nfan
    @9
    vx
    nfv
    nfan
    vx
    @12
    @13
    clt
    vx
    @11
    cabs
    vx
    cabs
    nfcv
    vx
    @10
    cC
    cmin
    vx
    @3
    @0
    vx
    cF
    cB
    vx
    cF
    nfcv
    @78
    nfres
    vx
    @3
    nfcv
    nffv
    vx
    cmin
    nfcv
    vx
    cC
    nfcv
    nfov
    nffv
    vx
    clt
    nfcv
    vx
    @13
    nfcv
    nfbr
    @47
    @48
    cA
    wcel
    #
    @50
    @14
    @47
    @79
    @50
    w3a
    #
    @12
    @48
    @18
    cfv
    #
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    @13
    clt
    @80
    @11
    @82
    cabs
    @80
    @10
    @81
    cC
    cmin
    @80
    @10
    @49
    @0
    cfv
    #
    @49
    cF
    cfv
    #
    @81
    @80
    @3
    @49
    @0
    @47
    @79
    @50
    simp3
    #
    fveq2d
    @80
    @49
    cB
    wcel
    @84
    @85
    wceq
    @80
    @3
    @49
    cB
    @86
    @47
    @79
    @45
    @50
    @53
    3ad2ant1
    eqeltrrd
    @49
    cB
    cF
    fvres
    syl
    @80
    @85
    @48
    cF
    cfv
    #
    @81
    @80
    wph
    @79
    @85
    @87
    wceq
    #
    @47
    @79
    wph
    @50
    @52
    3ad2ant1
    #
    @47
    @79
    @50
    simp2
    #
    wph
    @22
    cA
    wcel
    #
    wa
    #
    @66
    cF
    cfv
    #
    @22
    cF
    cfv
    #
    wceq
    #
    wi
    wph
    @79
    wa
    #
    @88
    wi
    vy
    vx
    @22
    @48
    wceq
    #
    @92
    @96
    @95
    @88
    @97
    @91
    @79
    wph
    @22
    @48
    cA
    eleq1
    anbi2d
    @97
    @93
    @85
    @94
    @87
    @97
    @66
    @49
    cF
    @22
    @48
    cT
    caddc
    oveq1
    fveq2d
    @22
    @48
    cF
    fveq2
    eqeq12d
    imbi12d
    limcperiod.fper
    chvarv
    syl2anc
    @80
    @79
    @81
    @87
    wceq
    @90
    @48
    cA
    cF
    fvres
    syl
    eqtr4d
    3eqtrd
    oveq1d
    fveq2d
    @80
    @33
    @79
    wa
    @48
    cD
    wne
    #
    @48
    cD
    cmin
    co
    #
    cabs
    cfv
    #
    @7
    clt
    wbr
    #
    wa
    #
    @83
    @13
    clt
    wbr
    #
    @80
    @33
    @79
    @47
    @79
    @33
    @50
    @21
    @43
    @33
    @45
    @9
    simpll3
    3ad2ant1
    @90
    jca
    @80
    @98
    @101
    @80
    @48
    cD
    @80
    @48
    cD
    wceq
    #
    @3
    @1
    wceq
    @80
    @3
    @1
    @4
    @8
    @46
    @79
    @50
    simp1rl
    neneqd
    @80
    @104
    @3
    @49
    @1
    @86
    @48
    cD
    cT
    caddc
    oveq1
    sylan9eq
    mtand
    neqned
    @80
    @100
    @6
    @7
    clt
    @80
    @99
    @5
    cabs
    @80
    @5
    @49
    @1
    cmin
    co
    @99
    @80
    @3
    @49
    @1
    cmin
    @86
    oveq1d
    @80
    @48
    cD
    cT
    @80
    wph
    @79
    @48
    cc
    wcel
    @89
    @90
    wph
    cA
    cc
    @48
    limcperiod.assc
    sselda
    syl2anc
    @80
    wph
    @41
    @89
    @42
    syl
    @80
    wph
    @76
    @89
    limcperiod.t
    syl
    pnpcan2d
    eqtr2d
    fveq2d
    @4
    @8
    @46
    @79
    @50
    simp1rr
    eqbrtrd
    jca
    @32
    @102
    @103
    wi
    vy
    @48
    cA
    @97
    @27
    @102
    @31
    @103
    @97
    @23
    @98
    @26
    @101
    @22
    @48
    cD
    neeq1
    @97
    @25
    @100
    @7
    clt
    @97
    @24
    @99
    cabs
    @22
    @48
    cD
    cmin
    oveq1
    fveq2d
    breq1d
    anbi12d
    @97
    @30
    @83
    @13
    clt
    @97
    @29
    @82
    cabs
    @97
    @28
    @81
    cC
    cmin
    @22
    @48
    @18
    fveq2
    oveq1d
    fveq2d
    breq1d
    imbi12d
    rspccva
    sylc
    eqbrtrd
    3exp
    rexlimd
    mpd
    ex
    ralrimiva
    3exp
    reximdvai
    mpd
    ralrimiva
    wph
    vw
    vz
    vb
    cB
    @1
    cC
    @0
    wph
    @37
    cc
    cB
    cF
    limcperiod.f
    limcperiod.bss
    fssresd
    @77
    wph
    cD
    cT
    @42
    limcperiod.t
    addcld
    ellimc3
    mpbir2and
end

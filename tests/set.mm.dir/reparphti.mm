include "ccom.mm"
include "cii.mm"
include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "cnco.mm"
include "syl2anc.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "cv.mm"
include "cmin.mm"
include "cfv.mm"
include "cmul.mm"
include "caddc.mm"
include "cmpt2.mm"
include "ctx.mm"
include "ctopon.mm"
include "iitopon.mm"
include "a1i.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "ctop.mm"
include "wss.mm"
include "eqid.mm"
include "cnfldtop.mm"
include "cnrest2r.mm"
include "mp1i.mm"
include "cnmpt2nd.mm"
include "cmpt.mm"
include "iirevcn.mm"
include "oveq2.mm"
include "cnmpt21.mm"
include "dfii3.mm"
include "oveq2i.mm"
include "syl6eleq.mm"
include "sseldd.mm"
include "cnmpt1st.mm"
include "cnmpt21f.mm"
include "mulcn.mm"
include "cnmpt22f.mm"
include "addcn.mm"
include "cc.mm"
include "crn.mm"
include "wb.mm"
include "cnfldtopon.mm"
include "cxp.mm"
include "wf.mm"
include "wral.mm"
include "wa.mm"
include "iiuni.mm"
include "cnf.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "adantrr.mm"
include "simprl.mm"
include "simprr.mm"
include "cr.mm"
include "w3a.mm"
include "wi.mm"
include "0re.mm"
include "1re.mm"
include "icccvx.mm"
include "mp2an.mm"
include "syl3anc.mm"
include "ralrimivva.mm"
include "fmpt2.mm"
include "sylib.mm"
include "frn.mm"
include "unitssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "cnrest2.mm"
include "mpbid.mm"
include "syl6eleqr.mm"
include "syl5eqel.mm"
include "sseldi.mm"
include "mulid2d.mm"
include "sseli.mm"
include "adantl.mm"
include "mul02d.mm"
include "oveq12d.mm"
include "addid1d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "wceq.mm"
include "simpr.mm"
include "0elunit.mm"
include "weq.mm"
include "oveq2d.mm"
include "1m0e1.mm"
include "syl6eq.mm"
include "simpl.mm"
include "fvex.mm"
include "ovmpt2a.mm"
include "sylancl.mm"
include "fvco3.mm"
include "sylan.mm"
include "3eqtr4d.mm"
include "1elunit.mm"
include "1m1e0.mm"
include "addid2d.mm"
include "adantr.mm"
include "ax-1cn.mm"
include "subcl.mm"
include "sylancr.mm"
include "mul01d.mm"
include "00id.mm"
include "mulid1d.mm"
include "npcan.mm"
include "isphtpy2d.mm"

theorem reparphti
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let vs: setvar s
  let vz: setvar z
  assume reparpht.2: |- ( ph -> F e. ( II Cn J ) )
  assume reparpht.3: |- ( ph -> G e. ( II Cn II ) )
  assume reparpht.4: |- ( ph -> ( G ` 0 ) = 0 )
  assume reparpht.5: |- ( ph -> ( G ` 1 ) = 1 )
  assume reparphti.6: |- H = ( x e. ( 0 [,] 1 ) , y e. ( 0 [,] 1 ) |-> ( F ` ( ( ( 1 - y ) x. ( G ` x ) ) + ( y x. x ) ) ) )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint J x
  disjoint J y
  disjoint ph x
  disjoint ph y
  disjoint s x
  disjoint s y
  disjoint F s
  disjoint G s
  disjoint H s
  disjoint J s
  disjoint s z
  disjoint ph s
  disjoint x z
  disjoint y z
  disjoint ph z
  assert |- ( ph -> H e. ( ( F o. G ) ( PHtpy ` J ) F ) )

  proof
    wph
    cF
    cG
    ccom
    #
    cF
    cH
    cJ
    vs
    wph
    cG
    cii
    cii
    ccn
    co
    #
    wcel
    #
    cF
    cii
    cJ
    ccn
    co
    #
    wcel
    @0
    @3
    wcel
    reparpht.3
    reparpht.2
    cG
    cF
    cii
    cii
    cJ
    cnco
    syl2anc
    reparpht.2
    wph
    cH
    vx
    vy
    cc0
    c1
    cicc
    co
    #
    @4
    c1
    vy
    cv
    #
    cmin
    co
    #
    vx
    cv
    #
    cG
    cfv
    #
    cmul
    co
    #
    @5
    @7
    cmul
    co
    #
    caddc
    co
    #
    cF
    cfv
    #
    cmpt2
    cii
    cii
    ctx
    co
    #
    cJ
    ccn
    co
    reparphti.6
    wph
    vx
    vy
    @11
    cF
    cii
    cii
    cii
    cJ
    @4
    @4
    cii
    @4
    ctopon
    cfv
    wcel
    wph
    iitopon
    a1i
    #
    @14
    wph
    vx
    vy
    @4
    @4
    @11
    cmpt2
    #
    @13
    ccnfld
    ctopn
    cfv
    #
    @4
    crest
    co
    #
    ccn
    co
    #
    @13
    cii
    ccn
    co
    #
    wph
    @15
    @13
    @16
    ccn
    co
    #
    wcel
    #
    @15
    @18
    wcel
    #
    wph
    vx
    vy
    @9
    @10
    caddc
    cii
    cii
    @16
    @16
    @16
    @4
    @4
    @14
    @14
    wph
    vx
    vy
    @6
    @8
    cmul
    cii
    cii
    @16
    @16
    @16
    @4
    @4
    @14
    @14
    wph
    @18
    @20
    vx
    vy
    @4
    @4
    @6
    cmpt2
    #
    @16
    ctop
    wcel
    @18
    @20
    wss
    wph
    @16
    @16
    eqid
    #
    cnfldtop
    @4
    @13
    @16
    cnrest2r
    mp1i
    #
    wph
    @23
    @19
    @18
    wph
    vx
    vy
    vz
    @5
    c1
    vz
    cv
    #
    cmin
    co
    #
    @6
    cii
    cii
    cii
    cii
    @4
    @4
    @4
    @14
    @14
    wph
    vx
    vy
    cii
    cii
    @4
    @4
    @14
    @14
    cnmpt2nd
    #
    @14
    vz
    @4
    @27
    cmpt
    @1
    wcel
    wph
    vz
    iirevcn
    a1i
    @26
    @5
    c1
    cmin
    oveq2
    cnmpt21
    cii
    @17
    @13
    ccn
    @16
    @24
    dfii3
    oveq2i
    #
    syl6eleq
    sseldd
    wph
    @18
    @20
    vx
    vy
    @4
    @4
    @8
    cmpt2
    #
    @25
    wph
    @30
    @19
    @18
    wph
    vx
    vy
    @7
    cG
    cii
    cii
    cii
    cii
    @4
    @4
    @14
    @14
    wph
    vx
    vy
    cii
    cii
    @4
    @4
    @14
    @14
    cnmpt1st
    #
    reparpht.3
    cnmpt21f
    @29
    syl6eleq
    sseldd
    cmul
    @16
    @16
    ctx
    co
    @16
    ccn
    co
    #
    wcel
    wph
    @16
    @24
    mulcn
    a1i
    #
    cnmpt22f
    wph
    vx
    vy
    @5
    @7
    cmul
    cii
    cii
    @16
    @16
    @16
    @4
    @4
    @14
    @14
    wph
    @18
    @20
    vx
    vy
    @4
    @4
    @5
    cmpt2
    #
    @25
    wph
    @34
    @19
    @18
    @28
    @29
    syl6eleq
    sseldd
    wph
    @18
    @20
    vx
    vy
    @4
    @4
    @7
    cmpt2
    #
    @25
    wph
    @35
    @19
    @18
    @31
    @29
    syl6eleq
    sseldd
    @33
    cnmpt22f
    caddc
    @32
    wcel
    wph
    @16
    @24
    addcn
    a1i
    cnmpt22f
    wph
    @16
    cc
    ctopon
    cfv
    wcel
    #
    @15
    crn
    @4
    wss
    #
    @4
    cc
    wss
    #
    @21
    @22
    wb
    @36
    wph
    @16
    @24
    cnfldtopon
    a1i
    wph
    @4
    @4
    cxp
    #
    @4
    @15
    wf
    #
    @37
    wph
    @11
    @4
    wcel
    #
    vy
    @4
    wral
    vx
    @4
    wral
    @40
    wph
    @41
    vx
    vy
    @4
    @4
    wph
    @7
    @4
    wcel
    #
    @5
    @4
    wcel
    #
    wa
    wa
    @8
    @4
    wcel
    #
    @42
    @43
    @41
    wph
    @42
    @44
    @43
    wph
    @4
    @4
    @7
    cG
    wph
    @2
    @4
    @4
    cG
    wf
    #
    reparpht.3
    cG
    cii
    cii
    @4
    @4
    iiuni
    iiuni
    cnf
    syl
    #
    ffvelrnda
    adantrr
    wph
    @42
    @43
    simprl
    wph
    @42
    @43
    simprr
    cc0
    cr
    wcel
    c1
    cr
    wcel
    @44
    @42
    @43
    w3a
    @41
    wi
    0re
    1re
    cc0
    c1
    @8
    @7
    @5
    icccvx
    mp2an
    syl3anc
    ralrimivva
    vx
    vy
    @4
    @4
    @11
    @4
    @15
    @15
    eqid
    fmpt2
    sylib
    @39
    @4
    @15
    frn
    syl
    @38
    wph
    @4
    cr
    cc
    unitssre
    ax-resscn
    sstri
    #
    a1i
    @4
    @15
    @13
    @16
    cc
    cnrest2
    syl3anc
    mpbid
    @29
    syl6eleqr
    reparpht.2
    cnmpt21f
    syl5eqel
    wph
    vs
    cv
    #
    @4
    wcel
    #
    wa
    #
    c1
    @48
    cG
    cfv
    #
    cmul
    co
    #
    cc0
    @48
    cmul
    co
    #
    caddc
    co
    #
    cF
    cfv
    #
    @51
    cF
    cfv
    #
    @48
    cc0
    cH
    co
    #
    @48
    @0
    cfv
    #
    @50
    @54
    @51
    cF
    @50
    @54
    @51
    cc0
    caddc
    co
    @51
    @50
    @52
    @51
    @53
    cc0
    caddc
    @50
    @51
    @50
    @4
    cc
    @51
    @47
    wph
    @4
    @4
    @48
    cG
    @46
    ffvelrnda
    sseldi
    #
    mulid2d
    @50
    @48
    @49
    @48
    cc
    wcel
    #
    wph
    @4
    cc
    @48
    @47
    sseli
    adantl
    #
    mul02d
    oveq12d
    @50
    @51
    @59
    addid1d
    eqtrd
    fveq2d
    @50
    @49
    cc0
    @4
    wcel
    #
    @57
    @55
    wceq
    wph
    @49
    simpr
    #
    0elunit
    vx
    vy
    @48
    cc0
    @4
    @4
    @12
    @55
    cH
    vx
    vs
    weq
    #
    @5
    cc0
    wceq
    #
    wa
    #
    @11
    @54
    cF
    @66
    @9
    @52
    @10
    @53
    caddc
    @66
    @6
    c1
    @8
    @51
    cmul
    @66
    @6
    c1
    cc0
    cmin
    co
    c1
    @66
    @5
    cc0
    c1
    cmin
    @64
    @65
    simpr
    #
    oveq2d
    1m0e1
    syl6eq
    @66
    @7
    @48
    cG
    @64
    @65
    simpl
    #
    fveq2d
    oveq12d
    @66
    @5
    cc0
    @7
    @48
    cmul
    @67
    @68
    oveq12d
    oveq12d
    fveq2d
    reparphti.6
    @54
    cF
    fvex
    ovmpt2a
    sylancl
    wph
    @45
    @49
    @58
    @56
    wceq
    @46
    @4
    @4
    @48
    cF
    cG
    fvco3
    sylan
    3eqtr4d
    @50
    @48
    c1
    cH
    co
    #
    cc0
    @51
    cmul
    co
    #
    c1
    @48
    cmul
    co
    #
    caddc
    co
    #
    cF
    cfv
    #
    @48
    cF
    cfv
    @50
    @49
    c1
    @4
    wcel
    #
    @69
    @73
    wceq
    @63
    1elunit
    vx
    vy
    @48
    c1
    @4
    @4
    @12
    @73
    cH
    @64
    @5
    c1
    wceq
    #
    wa
    #
    @11
    @72
    cF
    @76
    @9
    @70
    @10
    @71
    caddc
    @76
    @6
    cc0
    @8
    @51
    cmul
    @76
    @6
    c1
    c1
    cmin
    co
    cc0
    @76
    @5
    c1
    c1
    cmin
    @64
    @75
    simpr
    #
    oveq2d
    1m1e0
    syl6eq
    @76
    @7
    @48
    cG
    @64
    @75
    simpl
    #
    fveq2d
    oveq12d
    @76
    @5
    c1
    @7
    @48
    cmul
    @77
    @78
    oveq12d
    oveq12d
    fveq2d
    reparphti.6
    @72
    cF
    fvex
    ovmpt2a
    sylancl
    @50
    @72
    @48
    cF
    @50
    @72
    cc0
    @48
    caddc
    co
    @48
    @50
    @70
    cc0
    @71
    @48
    caddc
    @50
    @51
    @59
    mul02d
    @50
    @48
    @61
    mulid2d
    oveq12d
    @50
    @48
    @61
    addid2d
    eqtrd
    fveq2d
    eqtrd
    @50
    c1
    @48
    cmin
    co
    #
    cc0
    cG
    cfv
    #
    cmul
    co
    #
    @48
    cc0
    cmul
    co
    #
    caddc
    co
    #
    cF
    cfv
    #
    cc0
    cF
    cfv
    #
    cc0
    @48
    cH
    co
    #
    cc0
    @0
    cfv
    #
    @50
    @83
    cc0
    cF
    @50
    @83
    cc0
    cc0
    caddc
    co
    cc0
    @50
    @81
    cc0
    @82
    cc0
    caddc
    @50
    @81
    @79
    cc0
    cmul
    co
    cc0
    @50
    @80
    cc0
    @79
    cmul
    wph
    @80
    cc0
    wceq
    @49
    reparpht.4
    adantr
    oveq2d
    @50
    @79
    @50
    c1
    cc
    wcel
    #
    @60
    @79
    cc
    wcel
    ax-1cn
    @61
    c1
    @48
    subcl
    sylancr
    #
    mul01d
    eqtrd
    @50
    @48
    @61
    mul01d
    oveq12d
    00id
    syl6eq
    fveq2d
    @50
    @62
    @49
    @86
    @84
    wceq
    0elunit
    @63
    vx
    vy
    cc0
    @48
    @4
    @4
    @12
    @84
    cH
    @7
    cc0
    wceq
    #
    vy
    vs
    weq
    #
    wa
    #
    @11
    @83
    cF
    @92
    @9
    @81
    @10
    @82
    caddc
    @92
    @6
    @79
    @8
    @80
    cmul
    @92
    @5
    @48
    c1
    cmin
    @90
    @91
    simpr
    #
    oveq2d
    @92
    @7
    cc0
    cG
    @90
    @91
    simpl
    #
    fveq2d
    oveq12d
    @92
    @5
    @48
    @7
    cc0
    cmul
    @93
    @94
    oveq12d
    oveq12d
    fveq2d
    reparphti.6
    @83
    cF
    fvex
    ovmpt2a
    sylancr
    wph
    @87
    @85
    wceq
    @49
    wph
    @87
    @80
    cF
    cfv
    #
    @85
    wph
    @45
    @62
    @87
    @95
    wceq
    @46
    0elunit
    @4
    @4
    cc0
    cF
    cG
    fvco3
    sylancl
    wph
    @80
    cc0
    cF
    reparpht.4
    fveq2d
    eqtrd
    adantr
    3eqtr4d
    @50
    @79
    c1
    cG
    cfv
    #
    cmul
    co
    #
    @48
    c1
    cmul
    co
    #
    caddc
    co
    #
    cF
    cfv
    #
    c1
    cF
    cfv
    #
    c1
    @48
    cH
    co
    #
    c1
    @0
    cfv
    #
    @50
    @99
    c1
    cF
    @50
    @99
    @79
    @48
    caddc
    co
    #
    c1
    @50
    @97
    @79
    @98
    @48
    caddc
    @50
    @97
    @79
    c1
    cmul
    co
    @79
    @50
    @96
    c1
    @79
    cmul
    wph
    @96
    c1
    wceq
    @49
    reparpht.5
    adantr
    oveq2d
    @50
    @79
    @89
    mulid1d
    eqtrd
    @50
    @48
    @61
    mulid1d
    oveq12d
    @50
    @88
    @60
    @104
    c1
    wceq
    ax-1cn
    @61
    c1
    @48
    npcan
    sylancr
    eqtrd
    fveq2d
    @50
    @74
    @49
    @102
    @100
    wceq
    1elunit
    @63
    vx
    vy
    c1
    @48
    @4
    @4
    @12
    @100
    cH
    @7
    c1
    wceq
    #
    @91
    wa
    #
    @11
    @99
    cF
    @106
    @9
    @97
    @10
    @98
    caddc
    @106
    @6
    @79
    @8
    @96
    cmul
    @106
    @5
    @48
    c1
    cmin
    @105
    @91
    simpr
    #
    oveq2d
    @106
    @7
    c1
    cG
    @105
    @91
    simpl
    #
    fveq2d
    oveq12d
    @106
    @5
    @48
    @7
    c1
    cmul
    @107
    @108
    oveq12d
    oveq12d
    fveq2d
    reparphti.6
    @99
    cF
    fvex
    ovmpt2a
    sylancr
    wph
    @103
    @101
    wceq
    @49
    wph
    @103
    @96
    cF
    cfv
    #
    @101
    wph
    @45
    @74
    @103
    @109
    wceq
    @46
    1elunit
    @4
    @4
    c1
    cF
    cG
    fvco3
    sylancl
    wph
    @96
    c1
    cF
    reparpht.5
    fveq2d
    eqtrd
    adantr
    3eqtr4d
    isphtpy2d
end

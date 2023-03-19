include "cv.mm"
include "cbl.mm"
include "cfv.mm"
include "co.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "crp.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "wne.mm"
include "c1.mm"
include "1rp.mm"
include "ne0ii.mm"
include "ral0.mm"
include "simpr.mm"
include "raleqdv.mm"
include "mpbiri.mm"
include "ralrimivw.mm"
include "r19.2z.mm"
include "sylancr.mm"
include "cle.mm"
include "wbr.mm"
include "crn.mm"
include "wf.mm"
include "lebnumlem1.mm"
include "adantr.mm"
include "frn.mm"
include "syl.mm"
include "cuni.mm"
include "eqid.mm"
include "ccmp.mm"
include "wcel.mm"
include "ccn.mm"
include "lebnumlem2.mm"
include "cme.mm"
include "cxmt.mm"
include "metxmet.mm"
include "mopnuni.mm"
include "3syl.mm"
include "neeq1d.mm"
include "biimpa.mm"
include "evth2.mm"
include "wb.mm"
include "raleq.mm"
include "rexeqbi1dv.mm"
include "mpbird.mm"
include "wfn.mm"
include "ffn.mm"
include "breq1.mm"
include "ralbidv.mm"
include "rexrn.mm"
include "ssrexv.mm"
include "sylc.mm"
include "chash.mm"
include "cdiv.mm"
include "cn.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "eqnetrrd.mm"
include "unieq.mm"
include "uni0.mm"
include "syl6eq.mm"
include "necon3i.mm"
include "cfn.mm"
include "hashnncl.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "wn.mm"
include "ralnex.mm"
include "clt.mm"
include "cdif.mm"
include "cmpt.mm"
include "cxr.mm"
include "cinf.mm"
include "csu.mm"
include "cr.mm"
include "simprl.mm"
include "metdsval.mm"
include "difssd.mm"
include "elssuni.mm"
include "adantl.mm"
include "sseqtr4d.mm"
include "wi.mm"
include "eleq1.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "necon2ad.mm"
include "ad3antrrr.mm"
include "imp.mm"
include "pssdifn0.mm"
include "syl2anc.mm"
include "metdsre.mm"
include "syl3anc.mm"
include "ffvelrnd.mm"
include "eqeltrrd.mm"
include "rpred.mm"
include "simprr.mm"
include "sseq2.mm"
include "rspccva.mm"
include "sylan.mm"
include "cin.mm"
include "rpxrd.mm"
include "metdsge.mm"
include "syl31anc.mm"
include "blssm.mm"
include "difin0ss.mm"
include "syl5com.mm"
include "sylbid.mm"
include "mtod.mm"
include "ltnled.mm"
include "eqbrtrrd.mm"
include "fsumlt.mm"
include "oveq1.mm"
include "mpteq2dv.mm"
include "rneqd.mm"
include "infeq1d.mm"
include "sumeq2sdv.mm"
include "sumex.mm"
include "fvmpt.mm"
include "cmul.mm"
include "cc.mm"
include "rpcnd.mm"
include "fsumconst.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcan2d.mm"
include "eqtr2d.mm"
include "3brtr4d.mm"
include "mpbid.mm"
include "expr.mm"
include "syl5bir.mm"
include "con4d.mm"
include "ralimdva.mm"
include "oveq2.mm"
include "sseq1d.mm"
include "rexbidv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "pm2.61dane.mm"

theorem lebnumlem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let cD: class D
  let cU: class U
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let vd: setvar d
  let vm: setvar m
  let vr: setvar r
  let vw: setvar w
  assume lebnum.j: |- J = ( MetOpen ` D )
  assume lebnum.d: |- ( ph -> D e. ( Met ` X ) )
  assume lebnum.c: |- ( ph -> J e. Comp )
  assume lebnum.s: |- ( ph -> U C_ J )
  assume lebnum.u: |- ( ph -> X = U. U )
  assume lebnumlem1.u: |- ( ph -> U e. Fin )
  assume lebnumlem1.n: |- ( ph -> -. X e. U )
  assume lebnumlem1.f: |- F = ( y e. X |-> sum_ k e. U inf ( ran ( z e. ( X \ k ) |-> ( y D z ) ) , RR* , < ) )
  assume lebnumlem2.k: |- K = ( topGen ` ran (,) )

  disjoint d k
  disjoint d u
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint D d
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint D k
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint D u
  disjoint x y
  disjoint x z
  disjoint D x
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint J d
  disjoint J k
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint U d
  disjoint U k
  disjoint U u
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint F x
  disjoint d ph
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint X d
  disjoint X k
  disjoint X u
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint K x
  disjoint d m
  disjoint d r
  disjoint d w
  disjoint k m
  disjoint k r
  disjoint k w
  disjoint m r
  disjoint m u
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint D m
  disjoint r u
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint D r
  disjoint u w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint D w
  disjoint J w
  disjoint U m
  disjoint U r
  disjoint U w
  disjoint F r
  disjoint F w
  disjoint m ph
  disjoint ph r
  disjoint ph w
  disjoint X m
  disjoint X r
  disjoint X w
  assert |- ( ph -> E. d e. RR+ A. x e. X E. u e. U ( x ( ball ` D ) d ) C_ u )

  proof
    wph
    vx
    cv
    #
    vd
    cv
    #
    cD
    cbl
    cfv
    #
    co
    #
    vu
    cv
    #
    wss
    #
    vu
    cU
    wrex
    #
    vx
    cX
    wral
    #
    vd
    crp
    wrex
    #
    cX
    c0
    wph
    cX
    c0
    wceq
    #
    wa
    #
    crp
    c0
    wne
    @7
    vd
    crp
    wral
    @8
    c1
    crp
    1rp
    ne0ii
    @10
    @7
    vd
    crp
    @10
    @7
    @6
    vx
    c0
    wral
    @6
    vx
    ral0
    @10
    @6
    vx
    cX
    c0
    wph
    @9
    simpr
    raleqdv
    mpbiri
    ralrimivw
    @7
    vd
    crp
    r19.2z
    sylancr
    wph
    cX
    c0
    wne
    #
    wa
    #
    vr
    cv
    #
    @0
    cF
    cfv
    #
    cle
    wbr
    #
    vx
    cX
    wral
    #
    vr
    crp
    wrex
    #
    @8
    @12
    cF
    crn
    #
    crp
    wss
    #
    @16
    vr
    @18
    wrex
    #
    @17
    @12
    cX
    crp
    cF
    wf
    #
    @19
    wph
    @21
    @11
    wph
    vy
    vz
    cD
    cU
    vk
    cF
    cJ
    cX
    lebnum.j
    lebnum.d
    lebnum.c
    lebnum.s
    lebnum.u
    lebnumlem1.u
    lebnumlem1.n
    lebnumlem1.f
    lebnumlem1
    adantr
    #
    cX
    crp
    cF
    frn
    syl
    @12
    @20
    vw
    cv
    cF
    cfv
    #
    @14
    cle
    wbr
    #
    vx
    cX
    wral
    #
    vw
    cX
    wrex
    #
    @12
    @26
    @24
    vx
    cJ
    cuni
    #
    wral
    #
    vw
    @27
    wrex
    #
    @12
    vw
    vx
    cF
    cJ
    cK
    @27
    @27
    eqid
    lebnumlem2.k
    wph
    cJ
    ccmp
    wcel
    @11
    lebnum.c
    adantr
    wph
    cF
    cJ
    cK
    ccn
    co
    wcel
    @11
    wph
    vy
    vz
    cD
    cU
    vk
    cF
    cJ
    cK
    cX
    lebnum.j
    lebnum.d
    lebnum.c
    lebnum.s
    lebnum.u
    lebnumlem1.u
    lebnumlem1.n
    lebnumlem1.f
    lebnumlem2.k
    lebnumlem2
    adantr
    wph
    @11
    @27
    c0
    wne
    wph
    cX
    @27
    c0
    wph
    cD
    cX
    cme
    cfv
    wcel
    #
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cX
    @27
    wceq
    #
    lebnum.d
    cD
    cX
    metxmet
    #
    cD
    cJ
    cX
    lebnum.j
    mopnuni
    3syl
    #
    neeq1d
    biimpa
    evth2
    @12
    @32
    @26
    @29
    wb
    wph
    @32
    @11
    @34
    adantr
    @25
    @28
    vw
    cX
    @27
    @24
    vx
    cX
    @27
    raleq
    rexeqbi1dv
    syl
    mpbird
    @12
    @21
    cF
    cX
    wfn
    @20
    @26
    wb
    @22
    cX
    crp
    cF
    ffn
    @16
    @25
    vr
    vw
    cX
    cF
    @13
    @23
    wceq
    @15
    @24
    vx
    cX
    @13
    @23
    @14
    cle
    breq1
    ralbidv
    rexrn
    3syl
    mpbird
    @16
    vr
    @18
    crp
    ssrexv
    sylc
    @12
    @16
    @8
    vr
    crp
    @12
    @13
    crp
    wcel
    #
    wa
    #
    @13
    cU
    chash
    cfv
    #
    cdiv
    co
    #
    crp
    wcel
    #
    @16
    @0
    @38
    @2
    co
    #
    @4
    wss
    #
    vu
    cU
    wrex
    #
    vx
    cX
    wral
    #
    @8
    @36
    @13
    @37
    @12
    @35
    simpr
    @36
    @37
    @36
    @37
    cn
    wcel
    #
    cU
    c0
    wne
    #
    @36
    cU
    cuni
    #
    c0
    wne
    @45
    @36
    cX
    @46
    c0
    wph
    cX
    @46
    wceq
    #
    @11
    @35
    lebnum.u
    ad2antrr
    #
    wph
    @11
    @35
    simplr
    eqnetrrd
    cU
    c0
    @46
    c0
    cU
    c0
    wceq
    @46
    c0
    cuni
    c0
    cU
    c0
    unieq
    uni0
    syl6eq
    necon3i
    syl
    #
    @36
    cU
    cfn
    wcel
    #
    @44
    @45
    wb
    wph
    @50
    @11
    @35
    lebnumlem1.u
    ad2antrr
    #
    cU
    hashnncl
    syl
    mpbird
    #
    nnrpd
    rpdivcld
    #
    @36
    @15
    @42
    vx
    cX
    @36
    @0
    cX
    wcel
    #
    wa
    #
    @42
    @15
    @42
    wn
    @41
    wn
    #
    vu
    cU
    wral
    #
    @55
    @15
    wn
    #
    @41
    vu
    cU
    ralnex
    @36
    @54
    @57
    @58
    @36
    @54
    @57
    wa
    #
    wa
    #
    @14
    @13
    clt
    wbr
    @58
    @60
    cU
    vz
    cX
    vk
    cv
    #
    cdif
    #
    @0
    vz
    cv
    #
    cD
    co
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    cinf
    #
    vk
    csu
    #
    cU
    @38
    vk
    csu
    #
    @14
    @13
    clt
    @60
    cU
    @67
    @38
    vk
    @36
    @50
    @59
    @51
    adantr
    #
    @36
    @45
    @59
    @49
    adantr
    @60
    @61
    cU
    wcel
    #
    wa
    #
    @0
    vy
    cX
    vz
    @62
    vy
    cv
    #
    @63
    cD
    co
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    cinf
    #
    cmpt
    #
    cfv
    #
    @67
    cr
    @72
    @54
    @79
    @67
    wceq
    @60
    @54
    @71
    @36
    @54
    @57
    simprl
    #
    adantr
    #
    vy
    vz
    @0
    cD
    @62
    @78
    cX
    @78
    eqid
    #
    metdsval
    syl
    #
    @72
    cX
    cr
    @0
    @78
    @72
    @30
    @62
    cX
    wss
    #
    @62
    c0
    wne
    #
    cX
    cr
    @78
    wf
    @36
    @30
    @59
    @71
    wph
    @30
    @11
    @35
    lebnum.d
    ad2antrr
    ad2antrr
    #
    @72
    cX
    @61
    difssd
    #
    @72
    @61
    cX
    wss
    @61
    cX
    wne
    #
    @85
    @72
    @61
    @46
    cX
    @71
    @61
    @46
    wss
    @60
    @61
    cU
    elssuni
    adantl
    @36
    @47
    @59
    @71
    @48
    ad2antrr
    sseqtr4d
    @60
    @71
    @88
    wph
    @71
    @88
    wi
    @11
    @35
    @59
    wph
    @71
    @61
    cX
    wph
    @71
    wn
    @61
    cX
    wceq
    #
    cX
    cU
    wcel
    #
    wn
    lebnumlem1.n
    @89
    @71
    @90
    @61
    cX
    cU
    eleq1
    notbid
    syl5ibrcom
    necon2ad
    ad3antrrr
    imp
    @61
    cX
    pssdifn0
    syl2anc
    vy
    vz
    cD
    @62
    @78
    cX
    @82
    metdsre
    syl3anc
    @81
    ffvelrnd
    #
    eqeltrrd
    @72
    @38
    @36
    @39
    @59
    @71
    @53
    ad2antrr
    #
    rpred
    #
    @72
    @79
    @67
    @38
    clt
    @83
    @72
    @79
    @38
    clt
    wbr
    @38
    @79
    cle
    wbr
    #
    wn
    @72
    @94
    @40
    @61
    wss
    #
    @60
    @57
    @71
    @95
    wn
    #
    @36
    @54
    @57
    simprr
    @56
    @96
    vu
    @61
    cU
    @4
    @61
    wceq
    @41
    @95
    @4
    @61
    @40
    sseq2
    notbid
    rspccva
    sylan
    @72
    @94
    @62
    @40
    cin
    c0
    wceq
    #
    @95
    @72
    @31
    @84
    @54
    @38
    cxr
    wcel
    #
    @94
    @97
    wb
    @72
    @30
    @31
    @86
    @33
    syl
    #
    @87
    @81
    @72
    @38
    @92
    rpxrd
    #
    vy
    vz
    @0
    cD
    @38
    @62
    @78
    cX
    @82
    metdsge
    syl31anc
    @72
    @40
    cX
    wss
    #
    @97
    @95
    @72
    @31
    @54
    @98
    @101
    @99
    @81
    @100
    cD
    @0
    @38
    cX
    blssm
    syl3anc
    cX
    @61
    @40
    difin0ss
    syl5com
    sylbid
    mtod
    @72
    @79
    @38
    @91
    @93
    ltnled
    mpbird
    eqbrtrrd
    fsumlt
    @60
    @54
    @14
    @68
    wceq
    @80
    vy
    @0
    cU
    @77
    vk
    csu
    @68
    cX
    cF
    @73
    @0
    wceq
    #
    cU
    @77
    @67
    vk
    @102
    cxr
    @76
    @66
    clt
    @102
    @75
    @65
    @102
    vz
    @62
    @74
    @64
    @73
    @0
    @63
    cD
    oveq1
    mpteq2dv
    rneqd
    infeq1d
    sumeq2sdv
    lebnumlem1.f
    cU
    @67
    vk
    sumex
    fvmpt
    syl
    @60
    @69
    @37
    @38
    cmul
    co
    #
    @13
    @60
    @50
    @38
    cc
    wcel
    @69
    @103
    wceq
    @70
    @60
    @38
    @36
    @39
    @59
    @53
    adantr
    rpcnd
    cU
    @38
    vk
    fsumconst
    syl2anc
    @60
    @13
    @37
    @60
    @13
    @12
    @35
    @59
    simplr
    #
    rpcnd
    @60
    @37
    @36
    @44
    @59
    @52
    adantr
    #
    nncnd
    @60
    @37
    @105
    nnne0d
    divcan2d
    eqtr2d
    3brtr4d
    @60
    @14
    @13
    @60
    @14
    @60
    cX
    crp
    @0
    cF
    @12
    @21
    @35
    @59
    @22
    ad2antrr
    @80
    ffvelrnd
    rpred
    @60
    @13
    @104
    rpred
    ltnled
    mpbid
    expr
    syl5bir
    con4d
    ralimdva
    @7
    @43
    vd
    @38
    crp
    @1
    @38
    wceq
    #
    @6
    @42
    vx
    cX
    @106
    @5
    @41
    vu
    cU
    @106
    @3
    @40
    @4
    @1
    @38
    @0
    @2
    oveq2
    sseq1d
    rexbidv
    ralbidv
    rspcev
    syl6an
    rexlimdva
    mpd
    pm2.61dane
end

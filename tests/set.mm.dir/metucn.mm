include "cucn.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "ccnv.mm"
include "cc0.mm"
include "cico.mm"
include "cima.mm"
include "cmpt.mm"
include "crn.mm"
include "wrex.mm"
include "wa.mm"
include "clt.mm"
include "cxp.mm"
include "cfg.mm"
include "cmetu.mm"
include "cpsmet.mm"
include "wceq.mm"
include "metuval.mm"
include "syl.mm"
include "syl5eq.mm"
include "oveq12d.mm"
include "eleq2d.mm"
include "eqid.mm"
include "c0.mm"
include "wne.mm"
include "cust.mm"
include "oveq2.mm"
include "imaeq2d.mm"
include "cbvmptv.mm"
include "rneqi.mm"
include "metust.mm"
include "syl2anc.mm"
include "cfbas.mm"
include "metustfbas.mm"
include "isucn2.mm"
include "bitrd.mm"
include "wb.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpan2.mm"
include "adantl.mm"
include "metustel.mm"
include "adantr.mm"
include "mpbird.mm"
include "simpr.mm"
include "breqd.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "rexralbidv.mm"
include "ralxfr2d.mm"
include "imbi1d.mm"
include "2ralbidv.mm"
include "rexxfr2d.mm"
include "ad4antr.mm"
include "simplr.mm"
include "simprr.mm"
include "simprl.mm"
include "cbl.mm"
include "elbl4.mm"
include "cxr.mm"
include "rpxr.mm"
include "elbl3ps.mm"
include "sylanl2.mm"
include "bitr3d.mm"
include "syl22anc.mm"
include "simpllr.mm"
include "simp-4r.mm"
include "ffvelrnd.mm"
include "imbi12d.mm"
include "2ralbidva.mm"
include "rexbidva.mm"
include "ralbidva.mm"
include "pm5.32da.mm"

theorem metucn
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let cU: class U
  let cF: class F
  let cV: class V
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vd: setvar d
  let va: setvar a
  let ve: setvar e
  let vu: setvar u
  let vv: setvar v
  let vb: setvar b
  let vf: setvar f
  assume metucn.u: |- U = ( metUnif ` C )
  assume metucn.v: |- V = ( metUnif ` D )
  assume metucn.x: |- ( ph -> X =/= (/) )
  assume metucn.y: |- ( ph -> Y =/= (/) )
  assume metucn.c: |- ( ph -> C e. ( PsMet ` X ) )
  assume metucn.d: |- ( ph -> D e. ( PsMet ` Y ) )

  disjoint c d
  disjoint c x
  disjoint c y
  disjoint C c
  disjoint d x
  disjoint d y
  disjoint C d
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint D c
  disjoint D d
  disjoint D x
  disjoint D y
  disjoint F c
  disjoint F d
  disjoint F x
  disjoint F y
  disjoint U x
  disjoint U y
  disjoint V x
  disjoint X c
  disjoint X d
  disjoint X x
  disjoint X y
  disjoint Y c
  disjoint Y d
  disjoint Y x
  disjoint Y y
  disjoint c ph
  disjoint d ph
  disjoint ph x
  disjoint ph y
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint C a
  disjoint c e
  disjoint c u
  disjoint c v
  disjoint d e
  disjoint d u
  disjoint d v
  disjoint e u
  disjoint e v
  disjoint e x
  disjoint e y
  disjoint C e
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint C u
  disjoint v x
  disjoint v y
  disjoint C v
  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint D b
  disjoint c f
  disjoint d f
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint f y
  disjoint D f
  disjoint D u
  disjoint D v
  disjoint F u
  disjoint F v
  disjoint U u
  disjoint U v
  disjoint V u
  disjoint V v
  disjoint X a
  disjoint X e
  disjoint X u
  disjoint X v
  disjoint Y b
  disjoint Y f
  disjoint Y u
  disjoint Y v
  disjoint ph u
  disjoint ph v
  assert |- ( ph -> ( F e. ( U uCn V ) <-> ( F : X --> Y /\ A. d e. RR+ E. c e. RR+ A. x e. X A. y e. X ( ( x C y ) < c -> ( ( F ` x ) D ( F ` y ) ) < d ) ) ) )

  proof
    wph
    cF
    cU
    cV
    cucn
    co
    #
    wcel
    #
    cX
    cY
    cF
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    vu
    cv
    #
    wbr
    #
    @3
    cF
    cfv
    #
    @4
    cF
    cfv
    #
    vv
    cv
    #
    wbr
    #
    wi
    #
    vy
    cX
    wral
    #
    vx
    cX
    wral
    vu
    va
    crp
    cC
    ccnv
    #
    cc0
    va
    cv
    #
    cico
    co
    #
    cima
    #
    cmpt
    #
    crn
    #
    wrex
    #
    vv
    vb
    crp
    cD
    ccnv
    #
    cc0
    vb
    cv
    #
    cico
    co
    #
    cima
    #
    cmpt
    #
    crn
    #
    wral
    #
    wa
    #
    @2
    @3
    @4
    cC
    co
    vc
    cv
    #
    clt
    wbr
    #
    @7
    @8
    cD
    co
    vd
    cv
    #
    clt
    wbr
    #
    wi
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    vc
    crp
    wrex
    #
    vd
    crp
    wral
    #
    wa
    wph
    @1
    cF
    cX
    cX
    cxp
    #
    @18
    cfg
    co
    #
    cY
    cY
    cxp
    #
    @25
    cfg
    co
    #
    cucn
    co
    #
    wcel
    @27
    wph
    @0
    @40
    cF
    wph
    cU
    @37
    cV
    @39
    cucn
    wph
    cU
    cC
    cmetu
    cfv
    #
    @37
    metucn.u
    wph
    cC
    cX
    cpsmet
    cfv
    wcel
    #
    @41
    @37
    wceq
    metucn.c
    cC
    cX
    va
    metuval
    syl
    syl5eq
    wph
    cV
    cD
    cmetu
    cfv
    #
    @39
    metucn.v
    wph
    cD
    cY
    cpsmet
    cfv
    wcel
    #
    @43
    @39
    wceq
    metucn.d
    cD
    cY
    vb
    metuval
    syl
    syl5eq
    oveq12d
    eleq2d
    wph
    vx
    vy
    @18
    @25
    @37
    cF
    @39
    cX
    cY
    vv
    vu
    @37
    eqid
    @39
    eqid
    wph
    cX
    c0
    wne
    #
    @42
    @37
    cX
    cust
    cfv
    wcel
    metucn.x
    metucn.c
    cC
    @18
    cX
    vc
    @17
    vc
    crp
    @13
    cc0
    @28
    cico
    co
    #
    cima
    #
    cmpt
    va
    vc
    crp
    @16
    @47
    @14
    @28
    wceq
    @15
    @46
    @13
    @14
    @28
    cc0
    cico
    oveq2
    imaeq2d
    cbvmptv
    rneqi
    #
    metust
    syl2anc
    wph
    cY
    c0
    wne
    #
    @44
    @39
    cY
    cust
    cfv
    wcel
    metucn.y
    metucn.d
    cD
    @25
    cY
    vd
    @24
    vd
    crp
    @20
    cc0
    @30
    cico
    co
    #
    cima
    #
    cmpt
    vb
    vd
    crp
    @23
    @51
    @21
    @30
    wceq
    @22
    @50
    @20
    @21
    @30
    cc0
    cico
    oveq2
    imaeq2d
    cbvmptv
    rneqi
    #
    metust
    syl2anc
    wph
    @45
    @42
    @18
    @36
    cfbas
    cfv
    wcel
    metucn.x
    metucn.c
    cC
    @18
    cX
    ve
    @17
    ve
    crp
    @13
    cc0
    ve
    cv
    #
    cico
    co
    #
    cima
    #
    cmpt
    va
    ve
    crp
    @16
    @55
    @14
    @53
    wceq
    @15
    @54
    @13
    @14
    @53
    cc0
    cico
    oveq2
    imaeq2d
    cbvmptv
    rneqi
    #
    metustfbas
    syl2anc
    wph
    @49
    @44
    @25
    @38
    cfbas
    cfv
    wcel
    metucn.y
    metucn.d
    cD
    @25
    cY
    vf
    @24
    vf
    crp
    @20
    cc0
    vf
    cv
    #
    cico
    co
    #
    cima
    #
    cmpt
    vb
    vf
    crp
    @23
    @59
    @21
    @57
    wceq
    @22
    @58
    @20
    @21
    @57
    cc0
    cico
    oveq2
    imaeq2d
    cbvmptv
    rneqi
    #
    metustfbas
    syl2anc
    isucn2
    bitrd
    wph
    @2
    @26
    @35
    wph
    @2
    wa
    #
    @26
    @3
    @4
    @47
    wbr
    #
    @7
    @8
    @51
    wbr
    #
    wi
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    vc
    crp
    wrex
    #
    vd
    crp
    wral
    #
    @35
    wph
    @26
    @67
    wb
    @2
    wph
    @26
    @6
    @63
    wi
    #
    vy
    cX
    wral
    #
    vx
    cX
    wral
    #
    vu
    @18
    wrex
    #
    vd
    crp
    wral
    @67
    wph
    @19
    @71
    vv
    vd
    @51
    @25
    crp
    @25
    wph
    @30
    crp
    wcel
    #
    wa
    @51
    @25
    wcel
    #
    @51
    @59
    wceq
    #
    vf
    crp
    wrex
    #
    @72
    @75
    wph
    @72
    @51
    @51
    wceq
    #
    @75
    @51
    eqid
    @74
    @76
    vf
    @30
    crp
    @57
    @30
    wceq
    #
    @59
    @51
    @51
    @77
    @58
    @50
    @20
    @57
    @30
    cc0
    cico
    oveq2
    imaeq2d
    eqeq2d
    rspcev
    mpan2
    adantl
    wph
    @73
    @75
    wb
    #
    @72
    wph
    @44
    @78
    metucn.d
    @51
    cD
    @25
    cY
    vf
    @60
    metustel
    syl
    adantr
    mpbird
    wph
    @44
    @9
    @25
    wcel
    @9
    @51
    wceq
    #
    vd
    crp
    wrex
    wb
    metucn.d
    @9
    cD
    @25
    cY
    vd
    @52
    metustel
    syl
    wph
    @79
    wa
    #
    @12
    @69
    vu
    vx
    @18
    cX
    @80
    @11
    @68
    vy
    cX
    @80
    @10
    @63
    @6
    @80
    @9
    @51
    @7
    @8
    wph
    @79
    simpr
    breqd
    imbi2d
    ralbidv
    rexralbidv
    ralxfr2d
    wph
    @71
    @66
    vd
    crp
    wph
    @70
    @65
    vu
    vc
    @47
    @18
    crp
    @18
    wph
    @28
    crp
    wcel
    #
    wa
    @47
    @18
    wcel
    #
    @47
    @55
    wceq
    #
    ve
    crp
    wrex
    #
    @81
    @84
    wph
    @81
    @47
    @47
    wceq
    #
    @84
    @47
    eqid
    @83
    @85
    ve
    @28
    crp
    @53
    @28
    wceq
    #
    @55
    @47
    @47
    @86
    @54
    @46
    @13
    @53
    @28
    cc0
    cico
    oveq2
    imaeq2d
    eqeq2d
    rspcev
    mpan2
    adantl
    wph
    @82
    @84
    wb
    #
    @81
    wph
    @42
    @87
    metucn.c
    @47
    cC
    @18
    cX
    ve
    @56
    metustel
    syl
    adantr
    mpbird
    wph
    @42
    @5
    @18
    wcel
    @5
    @47
    wceq
    #
    vc
    crp
    wrex
    wb
    metucn.c
    @5
    cC
    @18
    cX
    vc
    @48
    metustel
    syl
    wph
    @88
    wa
    #
    @68
    @64
    vx
    vy
    cX
    cX
    @89
    @6
    @62
    @63
    @89
    @5
    @47
    @3
    @4
    wph
    @88
    simpr
    breqd
    imbi1d
    2ralbidv
    rexxfr2d
    ralbidv
    bitrd
    adantr
    @61
    @66
    @34
    vd
    crp
    @61
    @72
    wa
    #
    @65
    @33
    vc
    crp
    @90
    @81
    wa
    #
    @64
    @32
    vx
    vy
    cX
    cX
    @91
    @3
    cX
    wcel
    #
    @4
    cX
    wcel
    #
    wa
    #
    wa
    #
    @62
    @29
    @63
    @31
    @95
    @42
    @81
    @93
    @92
    @62
    @29
    wb
    wph
    @42
    @2
    @72
    @81
    @94
    metucn.c
    ad4antr
    @90
    @81
    @94
    simplr
    @91
    @92
    @93
    simprr
    #
    @91
    @92
    @93
    simprl
    #
    @42
    @81
    wa
    @93
    @92
    wa
    #
    wa
    @3
    @4
    @28
    cC
    cbl
    cfv
    co
    wcel
    #
    @62
    @29
    @4
    @3
    cC
    @28
    cX
    elbl4
    @81
    @42
    @28
    cxr
    wcel
    @98
    @99
    @29
    wb
    @28
    rpxr
    @3
    cC
    @4
    @28
    cX
    elbl3ps
    sylanl2
    bitr3d
    syl22anc
    @95
    @44
    @72
    @8
    cY
    wcel
    #
    @7
    cY
    wcel
    #
    @63
    @31
    wb
    wph
    @44
    @2
    @72
    @81
    @94
    metucn.d
    ad4antr
    @61
    @72
    @81
    @94
    simpllr
    @95
    cX
    cY
    @4
    cF
    wph
    @2
    @72
    @81
    @94
    simp-4r
    #
    @96
    ffvelrnd
    @95
    cX
    cY
    @3
    cF
    @102
    @97
    ffvelrnd
    @44
    @72
    wa
    @100
    @101
    wa
    #
    wa
    @7
    @8
    @30
    cD
    cbl
    cfv
    co
    wcel
    #
    @63
    @31
    @8
    @7
    cD
    @30
    cY
    elbl4
    @72
    @44
    @30
    cxr
    wcel
    @103
    @104
    @31
    wb
    @30
    rpxr
    @7
    cD
    @8
    @30
    cY
    elbl3ps
    sylanl2
    bitr3d
    syl22anc
    imbi12d
    2ralbidva
    rexbidva
    ralbidva
    bitrd
    pm5.32da
    bitrd
end

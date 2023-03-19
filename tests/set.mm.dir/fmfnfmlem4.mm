include "cv.mm"
include "wcel.mm"
include "wss.mm"
include "cima.mm"
include "ccnv.mm"
include "cmpt.mm"
include "crn.mm"
include "cun.mm"
include "cfi.mm"
include "cfv.mm"
include "wrex.mm"
include "wa.mm"
include "cfil.mm"
include "wi.mm"
include "filelss.mm"
include "ex.mm"
include "syl.mm"
include "cvv.mm"
include "cfbas.mm"
include "mptexg.mm"
include "rnexg.mm"
include "unexg.mm"
include "syl2anc.mm"
include "ssfii.mm"
include "unssbd.mm"
include "adantr.mm"
include "wceq.mm"
include "eqid.mm"
include "imaeq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpan2.mm"
include "adantl.mm"
include "wb.mm"
include "cdm.mm"
include "elfvdm.mm"
include "cnvimass.mm"
include "wf.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "ssexd.mm"
include "elrnmpt.mm"
include "mpbird.mm"
include "sseldd.mm"
include "wfun.mm"
include "ffun.mm"
include "ssid.mm"
include "funimass2.mm"
include "sylancl.mm"
include "sseq1d.mm"
include "jcad.mm"
include "cin.mm"
include "w3o.mm"
include "elfiun.mm"
include "fmfnfmlem1.mm"
include "fmfnfmlem3.mm"
include "eleq2d.mm"
include "vex.mm"
include "ax-mp.mm"
include "fmfnfmlem2.mm"
include "syl5bi.mm"
include "sylbid.mm"
include "syl6bb.mm"
include "fbssfi.mm"
include "sylan.mm"
include "ad3antrrr.mm"
include "cfm.mm"
include "co.mm"
include "w3a.mm"
include "cfg.mm"
include "filtop.mm"
include "3jca.mm"
include "ssfg.mm"
include "sselda.mm"
include "imaelfm.mm"
include "adantrr.mm"
include "jca.mm"
include "filin.mm"
include "3expa.mm"
include "simprr.mm"
include "wel.mm"
include "elin.mm"
include "fvelima.mm"
include "simplrr.mm"
include "simprl.mm"
include "ssel2.mm"
include "syl2an.mm"
include "ad2antrr.mm"
include "fbelss.mm"
include "sseqtr4d.mm"
include "fvimacnv.mm"
include "biimpd.mm"
include "impr.mm"
include "ad2ant2rl.mm"
include "elind.mm"
include "inss2.mm"
include "sstri.mm"
include "funfvima2.mm"
include "sylc.mm"
include "anassrs.mm"
include "expr.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "syld.mm"
include "impd.mm"
include "adantrl.mm"
include "ssrdv.mm"
include "sstrd.mm"
include "filss.mm"
include "syl13anc.mm"
include "exp32.mm"
include "ineq2.mm"
include "imaeq2d.mm"
include "imbi1d.mm"
include "syl5ibrcom.mm"
include "rexlimdvaa.mm"
include "imp.mm"
include "syldan.mm"
include "rexlimdvva.mm"
include "3jaod.mm"
include "rexlimdv.mm"
include "com23.mm"
include "impbid.mm"

theorem fmfnfmlem4
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cB: class B
  let cF: class F
  let cL: class L
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vf: setvar f
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume fmfnfm.b: |- ( ph -> B e. ( fBas ` Y ) )
  assume fmfnfm.l: |- ( ph -> L e. ( Fil ` X ) )
  assume fmfnfm.f: |- ( ph -> F : Y --> X )
  assume fmfnfm.fm: |- ( ph -> ( ( X FilMap F ) ` B ) C_ L )

  disjoint s t
  disjoint s x
  disjoint B s
  disjoint t x
  disjoint B t
  disjoint B x
  disjoint F s
  disjoint F t
  disjoint F x
  disjoint L s
  disjoint L t
  disjoint L x
  disjoint ph s
  disjoint ph t
  disjoint ph x
  disjoint X s
  disjoint X t
  disjoint X x
  disjoint Y s
  disjoint Y t
  disjoint Y x
  disjoint f s
  disjoint f t
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint s w
  disjoint s y
  disjoint s z
  disjoint t w
  disjoint t y
  disjoint t z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint F f
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint L f
  disjoint L w
  disjoint L y
  disjoint L z
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint X f
  disjoint X w
  disjoint X y
  disjoint X z
  disjoint Y f
  disjoint Y w
  disjoint Y z
  assert |- ( ph -> ( t e. L <-> ( t C_ X /\ E. s e. ( fi ` ( B u. ran ( x e. L |-> ( `' F " x ) ) ) ) ( F " s ) C_ t ) ) )

  proof
    wph
    vt
    cv
    #
    cL
    wcel
    #
    @0
    cX
    wss
    #
    cF
    vs
    cv
    #
    cima
    #
    @0
    wss
    #
    vs
    cB
    vx
    cL
    cF
    ccnv
    #
    vx
    cv
    #
    cima
    #
    cmpt
    #
    crn
    #
    cun
    #
    cfi
    cfv
    #
    wrex
    #
    wa
    wph
    @1
    @2
    @13
    wph
    cL
    cX
    cfil
    cfv
    #
    wcel
    #
    @1
    @2
    wi
    fmfnfm.l
    @15
    @1
    @2
    @0
    cL
    cX
    filelss
    ex
    syl
    wph
    @1
    @13
    wph
    @1
    wa
    #
    @6
    @0
    cima
    #
    @12
    wcel
    cF
    @17
    cima
    #
    @0
    wss
    #
    @13
    @16
    @10
    @12
    @17
    wph
    @10
    @12
    wss
    #
    @1
    wph
    @11
    cvv
    wcel
    #
    @20
    wph
    cB
    cY
    cfbas
    cfv
    #
    wcel
    #
    @10
    cvv
    wcel
    #
    @21
    fmfnfm.b
    wph
    @15
    @24
    fmfnfm.l
    @15
    @9
    cvv
    wcel
    @24
    vx
    cL
    @8
    @14
    mptexg
    @9
    cvv
    rnexg
    syl
    syl
    #
    cB
    @10
    @22
    cvv
    unexg
    syl2anc
    @21
    cB
    @10
    @12
    @11
    cvv
    ssfii
    unssbd
    syl
    adantr
    @16
    @17
    @10
    wcel
    #
    @17
    @8
    wceq
    #
    vx
    cL
    wrex
    #
    @1
    @28
    wph
    @1
    @17
    @17
    wceq
    #
    @28
    @17
    eqid
    @27
    @29
    vx
    @0
    cL
    @7
    @0
    wceq
    @8
    @17
    @17
    @7
    @0
    @6
    imaeq2
    eqeq2d
    rspcev
    mpan2
    adantl
    @16
    @17
    cvv
    wcel
    #
    @26
    @28
    wb
    wph
    @30
    @1
    wph
    @17
    cY
    cfbas
    cdm
    #
    wph
    @23
    cY
    @31
    wcel
    fmfnfm.b
    cB
    cY
    cfbas
    elfvdm
    syl
    wph
    cF
    cdm
    #
    @17
    cY
    cF
    @0
    cnvimass
    wph
    cY
    cX
    cF
    wf
    #
    @32
    cY
    wceq
    #
    fmfnfm.f
    cY
    cX
    cF
    fdm
    syl
    #
    syl5sseq
    ssexd
    adantr
    vx
    cL
    @8
    @17
    @9
    cvv
    @9
    eqid
    #
    elrnmpt
    syl
    mpbird
    sseldd
    wph
    @19
    @1
    wph
    @33
    @19
    fmfnfm.f
    @33
    cF
    wfun
    #
    @17
    @17
    wss
    @19
    cY
    cX
    cF
    ffun
    #
    @17
    ssid
    @17
    @0
    cF
    funimass2
    sylancl
    syl
    adantr
    @5
    @19
    vs
    @17
    @12
    @3
    @17
    wceq
    @4
    @18
    @0
    @3
    @17
    cF
    imaeq2
    sseq1d
    rspcev
    syl2anc
    ex
    jcad
    wph
    @2
    @13
    @1
    wph
    @13
    @2
    @1
    wph
    @5
    @2
    @1
    wi
    #
    vs
    @12
    wph
    @3
    @12
    wcel
    #
    @3
    cB
    cfi
    cfv
    #
    wcel
    #
    @3
    @10
    cfi
    cfv
    #
    wcel
    #
    @3
    vz
    cv
    #
    vw
    cv
    #
    cin
    #
    wceq
    #
    vw
    @43
    wrex
    vz
    @41
    wrex
    #
    w3o
    #
    @5
    @39
    wi
    #
    wph
    @23
    @24
    @40
    @50
    wb
    fmfnfm.b
    @25
    vz
    vw
    @3
    cB
    @10
    @22
    cvv
    elfiun
    syl2anc
    wph
    @42
    @51
    @44
    @49
    wph
    vt
    cB
    cF
    cL
    cX
    cY
    vs
    fmfnfm.b
    fmfnfm.l
    fmfnfm.f
    fmfnfm.fm
    fmfnfmlem1
    wph
    @44
    @3
    @10
    wcel
    #
    @51
    wph
    @43
    @10
    @3
    wph
    vx
    cB
    cF
    cL
    cX
    cY
    fmfnfm.b
    fmfnfm.l
    fmfnfm.f
    fmfnfm.fm
    fmfnfmlem3
    #
    eleq2d
    @52
    @3
    @8
    wceq
    vx
    cL
    wrex
    #
    wph
    @51
    @3
    cvv
    wcel
    @52
    @54
    wb
    vs
    vex
    vx
    cL
    @8
    @3
    @9
    cvv
    @36
    elrnmpt
    ax-mp
    wph
    vx
    vt
    cB
    cF
    cL
    cX
    cY
    vs
    fmfnfm.b
    fmfnfm.l
    fmfnfm.f
    fmfnfm.fm
    fmfnfmlem2
    syl5bi
    sylbid
    wph
    @48
    @51
    vz
    vw
    @41
    @43
    wph
    @45
    @41
    wcel
    #
    @46
    @43
    wcel
    #
    wa
    wa
    @51
    @48
    cF
    @47
    cima
    #
    @0
    wss
    #
    @39
    wi
    #
    wph
    @55
    @56
    @59
    wph
    @55
    wa
    @56
    @46
    @8
    wceq
    #
    vx
    cL
    wrex
    #
    @59
    wph
    @56
    @61
    wb
    @55
    wph
    @56
    @46
    @10
    wcel
    #
    @61
    wph
    @43
    @10
    @46
    @53
    eleq2d
    @46
    cvv
    wcel
    @62
    @61
    wb
    vw
    vex
    vx
    cL
    @8
    @46
    @9
    cvv
    @36
    elrnmpt
    ax-mp
    syl6bb
    adantr
    wph
    @55
    @3
    @45
    wss
    #
    vs
    cB
    wrex
    #
    @61
    @59
    wi
    #
    wph
    @23
    @55
    @64
    fmfnfm.b
    vs
    @45
    cB
    cY
    fbssfi
    sylan
    wph
    @64
    @65
    wph
    @63
    @65
    vs
    cB
    wph
    @3
    cB
    wcel
    #
    @63
    wa
    #
    wa
    #
    @60
    @59
    vx
    cL
    @68
    @7
    cL
    wcel
    #
    wa
    #
    @59
    @60
    cF
    @45
    @8
    cin
    #
    cima
    #
    @0
    wss
    #
    @39
    wi
    @70
    @73
    @2
    @1
    @70
    @73
    @2
    wa
    #
    wa
    #
    @15
    @4
    @7
    cin
    #
    cL
    wcel
    #
    @2
    @76
    @0
    wss
    @1
    wph
    @15
    @67
    @69
    @74
    fmfnfm.l
    ad3antrrr
    @70
    @77
    @74
    @68
    @15
    @4
    cL
    wcel
    #
    wa
    @69
    @77
    @68
    @15
    @78
    wph
    @15
    @67
    fmfnfm.l
    adantr
    wph
    @66
    @78
    @63
    wph
    @66
    wa
    #
    cB
    cX
    cF
    cfm
    co
    cfv
    #
    cL
    @4
    wph
    @80
    cL
    wss
    @66
    fmfnfm.fm
    adantr
    @79
    cX
    cL
    wcel
    #
    @23
    @33
    w3a
    #
    @3
    cY
    cB
    cfg
    co
    #
    wcel
    @4
    @80
    wcel
    wph
    @82
    @66
    wph
    @81
    @23
    @33
    wph
    @15
    @81
    fmfnfm.l
    cL
    cX
    filtop
    syl
    fmfnfm.b
    fmfnfm.f
    3jca
    adantr
    wph
    cB
    @83
    @3
    wph
    @23
    cB
    @83
    wss
    fmfnfm.b
    cB
    cY
    ssfg
    syl
    sselda
    cL
    cB
    @3
    cF
    @83
    cX
    cY
    @83
    eqid
    imaelfm
    syl2anc
    sseldd
    adantrr
    jca
    @15
    @78
    @69
    @77
    @4
    @7
    cL
    cX
    filin
    3expa
    sylan
    adantr
    @70
    @73
    @2
    simprr
    @75
    @76
    @72
    @0
    @75
    vw
    @76
    @72
    @70
    @2
    @46
    @76
    wcel
    #
    @46
    @72
    wcel
    #
    wi
    @73
    @84
    @46
    @4
    wcel
    #
    vw
    vx
    wel
    #
    wa
    @70
    @2
    wa
    #
    @85
    @46
    @4
    @7
    elin
    @88
    @86
    @87
    @85
    @88
    @86
    vy
    cv
    #
    cF
    cfv
    #
    @46
    wceq
    #
    vy
    @3
    wrex
    #
    @87
    @85
    wi
    #
    wph
    @86
    @92
    wi
    #
    @67
    @69
    @2
    wph
    @37
    @94
    wph
    @33
    @37
    fmfnfm.f
    @38
    syl
    #
    @37
    @86
    @92
    vy
    @46
    @3
    cF
    fvelima
    ex
    syl
    ad3antrrr
    @88
    @91
    @93
    vy
    @3
    @88
    vy
    vs
    wel
    #
    wa
    @90
    @7
    wcel
    #
    @90
    @72
    wcel
    #
    wi
    @91
    @93
    @88
    @96
    @97
    @98
    @70
    @2
    @96
    @97
    wa
    #
    @98
    @70
    @2
    @99
    wa
    #
    wa
    #
    @37
    @89
    @71
    wcel
    #
    @98
    wph
    @37
    @67
    @69
    @100
    @95
    ad3antrrr
    @101
    @45
    @8
    @89
    @70
    @63
    @96
    vy
    vz
    wel
    @100
    wph
    @66
    @63
    @69
    simplrr
    @2
    @96
    @97
    simprl
    @3
    @45
    @89
    ssel2
    syl2an
    @68
    @99
    @89
    @8
    wcel
    #
    @69
    @2
    @68
    @96
    @97
    @103
    @68
    @96
    wa
    #
    @97
    @103
    @104
    @37
    @89
    @32
    wcel
    @97
    @103
    wb
    wph
    @37
    @67
    @96
    @95
    ad2antrr
    @68
    @3
    @32
    @89
    wph
    @66
    @3
    @32
    wss
    @63
    @79
    @3
    cY
    @32
    wph
    @23
    @66
    @3
    cY
    wss
    fmfnfm.b
    cY
    cB
    @3
    fbelss
    sylan
    wph
    @34
    @66
    @35
    adantr
    sseqtr4d
    adantrr
    sselda
    @89
    @7
    cF
    fvimacnv
    syl2anc
    biimpd
    impr
    ad2ant2rl
    elind
    @37
    @71
    @32
    wss
    @102
    @98
    wi
    @71
    @8
    @32
    @45
    @8
    inss2
    cF
    @7
    cnvimass
    sstri
    @71
    @89
    cF
    funfvima2
    mpan2
    sylc
    anassrs
    expr
    @91
    @97
    @87
    @98
    @85
    @90
    @46
    @7
    eleq1
    @90
    @46
    @72
    eleq1
    imbi12d
    syl5ibcom
    rexlimdva
    syld
    impd
    syl5bi
    adantrl
    ssrdv
    @70
    @73
    @2
    simprl
    sstrd
    @76
    @0
    cL
    cX
    filss
    syl13anc
    exp32
    @60
    @58
    @73
    @39
    @60
    @57
    @72
    @0
    @60
    @47
    @71
    cF
    @46
    @8
    @45
    ineq2
    imaeq2d
    sseq1d
    imbi1d
    syl5ibrcom
    rexlimdva
    rexlimdvaa
    imp
    syldan
    sylbid
    impr
    @48
    @5
    @58
    @39
    @48
    @4
    @57
    @0
    @3
    @47
    cF
    imaeq2
    sseq1d
    imbi1d
    syl5ibrcom
    rexlimdvva
    3jaod
    sylbid
    rexlimdv
    com23
    impd
    impbid
end

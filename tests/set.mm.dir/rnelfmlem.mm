include "wcel.mm"
include "cfil.mm"
include "cfv.mm"
include "wf.mm"
include "w3a.mm"
include "crn.mm"
include "wa.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cmpt.mm"
include "cfbas.mm"
include "cpw.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wnel.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "simpl3.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "syl.mm"
include "wb.mm"
include "simpl1.mm"
include "elpw2g.mm"
include "mpbird.mm"
include "adantr.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "wceq.mm"
include "filtop.mm"
include "3ad2ant2.mm"
include "fimacnv.mm"
include "eqcomd.mm"
include "3ad2ant3.mm"
include "imaeq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "elrnmpt.mm"
include "3ad2ant1.mm"
include "ne0i.mm"
include "wn.mm"
include "0nelfil.mm"
include "cvv.mm"
include "0ex.mm"
include "ax-mp.mm"
include "wi.mm"
include "wal.mm"
include "wfn.mm"
include "ffn.mm"
include "fvelrnb.mm"
include "ad2antrr.mm"
include "eleq1.mm"
include "biimparc.mm"
include "ad2ant2l.mm"
include "adantll.mm"
include "wfun.mm"
include "ffun.mm"
include "ad3antrrr.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "3ad2antl3.mm"
include "adantlr.mm"
include "ad2ant2r.mm"
include "fvimacnv.mm"
include "mpbid.mm"
include "n0i.mm"
include "eqcom.mm"
include "sylnib.mm"
include "rexlimdvaa.mm"
include "sylbid.mm"
include "con2d.mm"
include "expr.mm"
include "com23.mm"
include "impr.mm"
include "alrimiv.mm"
include "imnan.mm"
include "elin.mm"
include "xchbinxr.mm"
include "albii.mm"
include "eq0.mm"
include "3bitr2i.mm"
include "sylib.mm"
include "simpll2.mm"
include "simprl.mm"
include "simplr.mm"
include "filin.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "syl5bi.mm"
include "mtod.mm"
include "df-nel.mm"
include "sylibr.mm"
include "vex.mm"
include "weq.mm"
include "cbvrexv.mm"
include "bitri.mm"
include "anbi12i.mm"
include "reeanv.mm"
include "bitr4i.mm"
include "3expb.mm"
include "eqidd.mm"
include "3adantl1.mm"
include "simpll1.mm"
include "ssexd.mm"
include "simprrl.mm"
include "simprrr.mm"
include "ineq12d.mm"
include "funcnvcnv.mm"
include "imain.mm"
include "3syl.mm"
include "eqtr4d.mm"
include "eqimss2.mm"
include "sseq1.mm"
include "exp32.mm"
include "rexlimdvv.mm"
include "ralrimivv.mm"
include "3jca.mm"
include "isfbas2.mm"
include "mpbir2and.mm"

theorem rnelfmlem
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cL: class L
  let cX: class X
  let cY: class Y
  let vb: setvar b
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint F x
  disjoint L x
  disjoint X x
  disjoint Y x
  disjoint b r
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F b
  disjoint F r
  disjoint F s
  disjoint F t
  disjoint F u
  disjoint F v
  disjoint F y
  disjoint F z
  disjoint L b
  disjoint L r
  disjoint L s
  disjoint L t
  disjoint L u
  disjoint L v
  disjoint L y
  disjoint L z
  disjoint X b
  disjoint X r
  disjoint X s
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X y
  disjoint X z
  disjoint Y b
  disjoint Y r
  disjoint Y s
  disjoint Y t
  disjoint Y u
  disjoint Y v
  disjoint Y y
  disjoint Y z
  assert |- ( ( ( Y e. A /\ L e. ( Fil ` X ) /\ F : Y --> X ) /\ ran F e. L ) -> ran ( x e. L |-> ( `' F " x ) ) e. ( fBas ` Y ) )

  proof
    cY
    cA
    wcel
    #
    cL
    cX
    cfil
    cfv
    wcel
    #
    cY
    cX
    cF
    wf
    #
    w3a
    #
    cF
    crn
    #
    cL
    wcel
    #
    wa
    #
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
    cY
    cfbas
    cfv
    wcel
    #
    @11
    cY
    cpw
    #
    wss
    #
    @11
    c0
    wne
    #
    c0
    @11
    wnel
    #
    vt
    cv
    #
    vr
    cv
    #
    vs
    cv
    #
    cin
    #
    wss
    #
    vt
    @11
    wrex
    #
    vs
    @11
    wral
    vr
    @11
    wral
    #
    w3a
    #
    @6
    cL
    @13
    @10
    wf
    @14
    @6
    vx
    cL
    @9
    @13
    @10
    @6
    @9
    @13
    wcel
    #
    @8
    cL
    wcel
    #
    @6
    @25
    @9
    cY
    wss
    #
    @6
    @2
    @27
    @0
    @1
    @2
    @5
    simpl3
    @2
    cF
    cdm
    #
    @9
    cY
    cF
    @8
    cnvimass
    cY
    cX
    cF
    fdm
    #
    syl5sseq
    syl
    @6
    @0
    @25
    @27
    wb
    @0
    @1
    @2
    @5
    simpl1
    #
    @9
    cY
    cA
    elpw2g
    syl
    mpbird
    adantr
    @10
    eqid
    #
    fmptd
    cL
    @13
    @10
    frn
    syl
    @6
    @15
    @16
    @23
    @6
    cY
    @11
    wcel
    #
    @15
    @6
    @32
    cY
    @9
    wceq
    #
    vx
    cL
    wrex
    #
    @6
    cX
    cL
    wcel
    #
    cY
    @7
    cX
    cima
    #
    wceq
    #
    @34
    @3
    @35
    @5
    @1
    @0
    @35
    @2
    cL
    cX
    filtop
    3ad2ant2
    adantr
    @3
    @37
    @5
    @2
    @0
    @37
    @1
    @2
    @36
    cY
    cY
    cX
    cF
    fimacnv
    eqcomd
    3ad2ant3
    adantr
    @33
    @37
    vx
    cX
    cL
    @8
    cX
    wceq
    @9
    @36
    cY
    @8
    cX
    @7
    imaeq2
    eqeq2d
    rspcev
    syl2anc
    @3
    @32
    @34
    wb
    #
    @5
    @0
    @1
    @38
    @2
    vx
    cL
    @9
    cY
    @10
    cA
    @31
    elrnmpt
    3ad2ant1
    adantr
    mpbird
    @11
    cY
    ne0i
    syl
    @6
    c0
    @11
    wcel
    #
    wn
    @16
    @6
    @39
    c0
    cL
    wcel
    #
    @3
    @40
    wn
    #
    @5
    @1
    @0
    @41
    @2
    cL
    cX
    0nelfil
    3ad2ant2
    adantr
    @39
    c0
    @9
    wceq
    #
    vx
    cL
    wrex
    #
    @6
    @40
    c0
    cvv
    wcel
    @39
    @43
    wb
    0ex
    vx
    cL
    @9
    c0
    @10
    cvv
    @31
    elrnmpt
    ax-mp
    @6
    @42
    @40
    vx
    cL
    @6
    @26
    @42
    wa
    #
    wa
    #
    c0
    @8
    @4
    cin
    #
    cL
    @45
    vy
    cv
    #
    @8
    wcel
    #
    @47
    @4
    wcel
    #
    wn
    #
    wi
    #
    vy
    wal
    #
    c0
    @46
    wceq
    #
    @45
    @51
    vy
    @6
    @26
    @42
    @51
    @6
    @26
    wa
    @48
    @42
    @50
    @6
    @26
    @48
    @42
    @50
    wi
    @6
    @26
    @48
    wa
    #
    wa
    #
    @49
    @42
    @55
    @49
    vz
    cv
    #
    cF
    cfv
    #
    @47
    wceq
    #
    vz
    cY
    wrex
    #
    @42
    wn
    #
    @3
    @49
    @59
    wb
    #
    @5
    @54
    @2
    @0
    @61
    @1
    @2
    cF
    cY
    wfn
    @61
    cY
    cX
    cF
    ffn
    vz
    cY
    @47
    cF
    fvelrnb
    syl
    3ad2ant3
    ad2antrr
    @55
    @58
    @60
    vz
    cY
    @55
    @56
    cY
    wcel
    #
    @58
    wa
    #
    wa
    #
    @56
    @9
    wcel
    #
    @60
    @64
    @57
    @8
    wcel
    #
    @65
    @54
    @63
    @66
    @6
    @48
    @58
    @66
    @26
    @62
    @58
    @66
    @48
    @57
    @47
    @8
    eleq1
    biimparc
    ad2ant2l
    adantll
    @64
    cF
    wfun
    #
    @56
    @28
    wcel
    #
    @66
    @65
    wb
    @3
    @67
    @5
    @54
    @63
    @2
    @0
    @67
    @1
    cY
    cX
    cF
    ffun
    #
    3ad2ant3
    ad3antrrr
    @6
    @62
    @68
    @54
    @58
    @3
    @62
    @68
    @5
    @2
    @0
    @62
    @68
    @1
    @2
    @68
    @62
    @2
    @28
    cY
    @56
    @29
    eleq2d
    biimpar
    3ad2antl3
    adantlr
    ad2ant2r
    @56
    @8
    cF
    fvimacnv
    syl2anc
    mpbid
    @65
    @9
    c0
    wceq
    @42
    @9
    @56
    n0i
    @9
    c0
    eqcom
    sylnib
    syl
    rexlimdvaa
    sylbid
    con2d
    expr
    com23
    impr
    alrimiv
    @52
    @47
    @46
    wcel
    #
    wn
    #
    vy
    wal
    @46
    c0
    wceq
    @53
    @51
    @71
    vy
    @51
    @48
    @49
    wa
    @70
    @48
    @49
    imnan
    @47
    @8
    @4
    elin
    xchbinxr
    albii
    vy
    @46
    eq0
    @46
    c0
    eqcom
    3bitr2i
    sylib
    @45
    @1
    @26
    @5
    @46
    cL
    wcel
    @0
    @1
    @2
    @5
    @44
    simpll2
    @6
    @26
    @42
    simprl
    @3
    @5
    @44
    simplr
    @8
    @4
    cL
    cX
    filin
    syl3anc
    eqeltrd
    rexlimdvaa
    syl5bi
    mtod
    c0
    @11
    df-nel
    sylibr
    @6
    @22
    vr
    vs
    @11
    @11
    @18
    @11
    wcel
    #
    @19
    @11
    wcel
    #
    wa
    #
    @18
    @7
    vu
    cv
    #
    cima
    #
    wceq
    #
    @19
    @7
    vv
    cv
    #
    cima
    #
    wceq
    #
    wa
    #
    vv
    cL
    wrex
    vu
    cL
    wrex
    #
    @6
    @22
    @74
    @77
    vu
    cL
    wrex
    #
    @80
    vv
    cL
    wrex
    #
    wa
    @82
    @72
    @83
    @73
    @84
    @72
    @18
    @9
    wceq
    #
    vx
    cL
    wrex
    #
    @83
    @18
    cvv
    wcel
    @72
    @86
    wb
    vr
    vex
    vx
    cL
    @9
    @18
    @10
    cvv
    @31
    elrnmpt
    ax-mp
    @85
    @77
    vx
    vu
    cL
    vx
    vu
    weq
    @9
    @76
    @18
    @8
    @75
    @7
    imaeq2
    eqeq2d
    cbvrexv
    bitri
    @73
    @19
    @9
    wceq
    #
    vx
    cL
    wrex
    #
    @84
    @19
    cvv
    wcel
    @73
    @88
    wb
    vs
    vex
    vx
    cL
    @9
    @19
    @10
    cvv
    @31
    elrnmpt
    ax-mp
    @87
    @80
    vx
    vv
    cL
    vx
    vv
    weq
    @9
    @79
    @19
    @8
    @78
    @7
    imaeq2
    eqeq2d
    cbvrexv
    bitri
    anbi12i
    @77
    @80
    vu
    vv
    cL
    cL
    reeanv
    bitr4i
    @6
    @81
    @22
    vu
    vv
    cL
    cL
    @6
    @75
    cL
    wcel
    #
    @78
    cL
    wcel
    #
    wa
    #
    @81
    @22
    @6
    @91
    @81
    wa
    #
    wa
    #
    @7
    @75
    @78
    cin
    #
    cima
    #
    @11
    wcel
    #
    @95
    @20
    wss
    #
    @22
    @93
    @96
    @95
    @9
    wceq
    #
    vx
    cL
    wrex
    #
    @3
    @91
    @99
    @5
    @81
    @1
    @2
    @91
    @99
    @0
    @1
    @2
    wa
    @91
    wa
    #
    @94
    cL
    wcel
    #
    @95
    @95
    wceq
    #
    @99
    @1
    @91
    @101
    @2
    @1
    @89
    @90
    @101
    @75
    @78
    cL
    cX
    filin
    3expb
    adantlr
    @100
    @95
    eqidd
    @98
    @102
    vx
    @94
    cL
    @8
    @94
    wceq
    @9
    @95
    @95
    @8
    @94
    @7
    imaeq2
    eqeq2d
    rspcev
    syl2anc
    3adantl1
    ad2ant2r
    @93
    @95
    cvv
    wcel
    @96
    @99
    wb
    @93
    @95
    cY
    cA
    @0
    @1
    @2
    @5
    @92
    simpll1
    @3
    @95
    cY
    wss
    #
    @5
    @92
    @2
    @0
    @103
    @1
    @2
    @28
    @95
    cY
    cF
    @94
    cnvimass
    @29
    syl5sseq
    3ad2ant3
    ad2antrr
    ssexd
    vx
    cL
    @9
    @95
    @10
    cvv
    @31
    elrnmpt
    syl
    mpbird
    @93
    @20
    @95
    wceq
    @97
    @93
    @20
    @76
    @79
    cin
    #
    @95
    @93
    @18
    @76
    @19
    @79
    @6
    @91
    @77
    @80
    simprrl
    @6
    @91
    @77
    @80
    simprrr
    ineq12d
    @3
    @95
    @104
    wceq
    #
    @5
    @92
    @2
    @0
    @105
    @1
    @2
    @67
    @7
    ccnv
    wfun
    @105
    @69
    cF
    funcnvcnv
    @75
    @78
    @7
    imain
    3syl
    3ad2ant3
    ad2antrr
    eqtr4d
    @95
    @20
    eqimss2
    syl
    @21
    @97
    vt
    @95
    @11
    @17
    @95
    @20
    sseq1
    rspcev
    syl2anc
    exp32
    rexlimdvv
    syl5bi
    ralrimivv
    3jca
    @6
    @0
    @12
    @14
    @24
    wa
    wb
    @30
    vr
    vs
    vt
    cA
    cY
    @11
    isfbas2
    syl
    mpbir2and
end

include "wcel.mm"
include "w3a.mm"
include "ctcl.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "wss.mm"
include "ccom.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "csn.mm"
include "cima.mm"
include "cun.mm"
include "cop.mm"
include "wb.mm"
include "df-br.mm"
include "a1i.mm"
include "trclfv.mm"
include "breqd.mm"
include "3ad2ant3.mm"
include "elimasng.mm"
include "3adant3.mm"
include "3bitr4d.mm"
include "wceq.mm"
include "wrex.mm"
include "intimasn.mm"
include "3ad2ant1.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "cxp.mm"
include "wsbc.mm"
include "cvv.mm"
include "simpl3.mm"
include "snex.mm"
include "vex.mm"
include "xpex.mm"
include "unexg.mm"
include "sylancl.mm"
include "trclfvlb.mm"
include "unssad.mm"
include "syl.mm"
include "trclfvcotrg.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "simpl1.mm"
include "snidg.mm"
include "inelcm.mm"
include "syl2anc.mm"
include "xpima2.mm"
include "unssbd.mm"
include "imass1.mm"
include "eqsstr3d.mm"
include "imaundir.mm"
include "simpr.mm"
include "crn.mm"
include "imassrn.mm"
include "rnxpss.mm"
include "sstri.mm"
include "unssd.mm"
include "syl5eqss.mm"
include "trclimalb2.mm"
include "eqssd.mm"
include "sbcan.mm"
include "csb.mm"
include "fvex.mm"
include "sbcssg.mm"
include "ax-mp.mm"
include "csbconstg.mm"
include "csbvarg.mm"
include "sseq12i.mm"
include "bitri.mm"
include "csbcog.mm"
include "coeq12i.mm"
include "eqtri.mm"
include "anbi12i.mm"
include "sbceq2g.mm"
include "csbima12.mm"
include "imaeq1i.mm"
include "imaeq2i.mm"
include "3eqtri.mm"
include "eqeq2i.mm"
include "sylbbr.mm"
include "syl21anc.mm"
include "spesbcd.mm"
include "ex.mm"
include "weq.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "imaeq1.mm"
include "eqeq2d.mm"
include "rexab2.mm"
include "syl6bb.mm"
include "elab.mm"
include "syl6ibr.mm"
include "intss1.mm"
include "syl6.mm"
include "alrimiv.mm"
include "ssintab.mm"
include "sylibr.mm"
include "adantr.mm"
include "imaco.mm"
include "syl5eqssr.mm"
include "sylan9ss.mm"
include "jca.mm"
include "imaexg.mm"
include "imaundi.mm"
include "sseq1i.mm"
include "unss.mm"
include "bitr4i.mm"
include "imaeq2.mm"
include "id.mm"
include "sseq12d.mm"
include "cleq2lem.mm"
include "syl5bb.mm"
include "eqeltrd.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "mpgbir.mm"
include "eqtrd.mm"
include "eleq2d.mm"
include "bitrd.mm"

theorem brtrclfv2
  let cR: class R
  let cU: class U
  let vf: setvar f
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vg: setvar g
  let vr: setvar r
  let vs: setvar s

  disjoint R f
  disjoint U f
  disjoint V f
  disjoint W f
  disjoint X f
  disjoint Y f
  disjoint f g
  disjoint f r
  disjoint f s
  disjoint g r
  disjoint g s
  disjoint R g
  disjoint r s
  disjoint R r
  disjoint R s
  disjoint X g
  disjoint X r
  disjoint X s
  assert |- ( ( X e. U /\ Y e. V /\ R e. W ) -> ( X ( t+ ` R ) Y <-> Y e. |^| { f | ( R " ( { X } u. f ) ) C_ f } ) )

  proof
    cX
    cU
    wcel
    #
    cY
    cV
    wcel
    #
    cR
    cW
    wcel
    #
    w3a
    #
    cX
    cY
    cR
    ctcl
    cfv
    #
    wbr
    #
    cY
    cR
    vr
    cv
    #
    wss
    #
    @6
    @6
    ccom
    #
    @6
    wss
    #
    wa
    #
    vr
    cab
    #
    cint
    #
    cX
    csn
    #
    cima
    #
    wcel
    #
    cY
    cR
    @13
    vf
    cv
    #
    cun
    #
    cima
    #
    @16
    wss
    #
    vf
    cab
    #
    cint
    #
    wcel
    @3
    cX
    cY
    @12
    wbr
    #
    cX
    cY
    cop
    @12
    wcel
    #
    @5
    @15
    @22
    @23
    wb
    @3
    cX
    cY
    @12
    df-br
    a1i
    @2
    @0
    @5
    @22
    wb
    @1
    @2
    @4
    @12
    cX
    cY
    vr
    cR
    cW
    trclfv
    breqd
    3ad2ant3
    @0
    @1
    @15
    @23
    wb
    @2
    @12
    cX
    cY
    cU
    cV
    elimasng
    3adant3
    3bitr4d
    @3
    @14
    @21
    cY
    @3
    @14
    vg
    cv
    #
    vs
    cv
    #
    @13
    cima
    #
    wceq
    #
    vs
    @11
    wrex
    #
    vg
    cab
    #
    cint
    #
    @21
    @0
    @1
    @14
    @30
    wceq
    @2
    vg
    @11
    cX
    cU
    vs
    intimasn
    3ad2ant1
    @3
    @30
    @21
    @3
    @19
    @30
    @16
    wss
    #
    wi
    #
    vf
    wal
    @30
    @21
    wss
    @3
    @32
    vf
    @3
    @19
    @16
    @29
    wcel
    #
    @31
    @3
    @19
    @10
    @16
    @6
    @13
    cima
    #
    wceq
    #
    wa
    #
    vr
    wex
    #
    @33
    @3
    @19
    @37
    @3
    @19
    wa
    #
    @36
    vr
    cR
    @13
    @16
    cxp
    #
    cun
    #
    ctcl
    cfv
    #
    @38
    cR
    @41
    wss
    #
    @41
    @41
    ccom
    #
    @41
    wss
    #
    @16
    @41
    @13
    cima
    #
    wceq
    #
    @36
    vr
    @41
    wsbc
    #
    @38
    @40
    cvv
    wcel
    #
    @42
    @38
    @2
    @39
    cvv
    wcel
    @48
    @0
    @1
    @2
    @19
    simpl3
    @13
    @16
    cX
    snex
    vf
    vex
    #
    xpex
    cR
    @39
    cW
    cvv
    unexg
    sylancl
    #
    @48
    cR
    @39
    @41
    @40
    cvv
    trclfvlb
    #
    unssad
    syl
    @44
    @38
    @40
    trclfvcotrg
    a1i
    @38
    @16
    @45
    @38
    @16
    @39
    @13
    cima
    #
    @45
    @38
    @13
    @13
    cin
    c0
    wne
    #
    @52
    @16
    wceq
    @38
    cX
    @13
    wcel
    #
    @54
    @53
    @38
    @0
    @54
    @0
    @1
    @2
    @19
    simpl1
    cX
    cU
    snidg
    syl
    #
    @55
    cX
    @13
    @13
    inelcm
    syl2anc
    @13
    @16
    @13
    xpima2
    syl
    @38
    @39
    @41
    wss
    @52
    @45
    wss
    @38
    cR
    @39
    @41
    @38
    @48
    @40
    @41
    wss
    @50
    @51
    syl
    unssbd
    @39
    @41
    @13
    imass1
    syl
    eqsstr3d
    @38
    @48
    @40
    @17
    cima
    #
    @16
    wss
    @45
    @16
    wss
    @50
    @38
    @56
    @18
    @39
    @17
    cima
    #
    cun
    @16
    cR
    @39
    @17
    imaundir
    @38
    @18
    @57
    @16
    @3
    @19
    simpr
    @57
    @16
    wss
    @38
    @57
    @39
    crn
    @16
    @39
    @17
    imassrn
    @13
    @16
    rnxpss
    sstri
    a1i
    unssd
    syl5eqss
    @13
    @16
    @40
    cvv
    trclimalb2
    syl2anc
    eqssd
    @47
    @10
    vr
    @41
    wsbc
    #
    @35
    vr
    @41
    wsbc
    #
    wa
    @42
    @44
    wa
    #
    @46
    wa
    @10
    @35
    vr
    @41
    sbcan
    @58
    @60
    @59
    @46
    @58
    @7
    vr
    @41
    wsbc
    #
    @9
    vr
    @41
    wsbc
    #
    wa
    @60
    @7
    @9
    vr
    @41
    sbcan
    @61
    @42
    @62
    @44
    @61
    vr
    @41
    cR
    csb
    #
    vr
    @41
    @6
    csb
    #
    wss
    #
    @42
    @41
    cvv
    wcel
    #
    @61
    @65
    wb
    @40
    ctcl
    fvex
    #
    vr
    @41
    cR
    @6
    cvv
    sbcssg
    ax-mp
    @63
    cR
    @64
    @41
    @66
    @63
    cR
    wceq
    @67
    vr
    @41
    cR
    cvv
    csbconstg
    ax-mp
    @66
    @64
    @41
    wceq
    @67
    vr
    @41
    cvv
    csbvarg
    ax-mp
    #
    sseq12i
    bitri
    @62
    vr
    @41
    @8
    csb
    #
    @64
    wss
    #
    @44
    @66
    @62
    @70
    wb
    @67
    vr
    @41
    @8
    @6
    cvv
    sbcssg
    ax-mp
    @69
    @43
    @64
    @41
    @69
    @64
    @64
    ccom
    #
    @43
    @66
    @69
    @71
    wceq
    @67
    vr
    @41
    @6
    @6
    cvv
    csbcog
    ax-mp
    @64
    @41
    @64
    @41
    @68
    @68
    coeq12i
    eqtri
    @68
    sseq12i
    bitri
    anbi12i
    bitri
    @59
    @16
    vr
    @41
    @34
    csb
    #
    wceq
    #
    @46
    @66
    @59
    @73
    wb
    @67
    vr
    @41
    @16
    @34
    cvv
    sbceq2g
    ax-mp
    @72
    @45
    @16
    @72
    @64
    vr
    @41
    @13
    csb
    #
    cima
    @41
    @74
    cima
    @45
    vr
    @41
    @13
    @6
    csbima12
    @64
    @41
    @74
    @68
    imaeq1i
    @74
    @13
    @41
    @66
    @74
    @13
    wceq
    @67
    vr
    @41
    @13
    cvv
    csbconstg
    ax-mp
    imaeq2i
    3eqtri
    eqeq2i
    bitri
    anbi12i
    sylbbr
    syl21anc
    spesbcd
    ex
    @28
    @37
    vg
    @16
    @49
    vg
    vf
    weq
    #
    @28
    @16
    @26
    wceq
    #
    vs
    @11
    wrex
    @37
    @75
    @27
    @76
    vs
    @11
    @24
    @16
    @26
    eqeq1
    rexbidv
    @10
    @76
    @35
    vs
    vr
    vs
    vr
    weq
    #
    @26
    @34
    @16
    @25
    @6
    @13
    imaeq1
    #
    eqeq2d
    rexab2
    syl6bb
    elab
    syl6ibr
    @16
    @29
    intss1
    syl6
    alrimiv
    @19
    vf
    @30
    ssintab
    sylibr
    @21
    @30
    wss
    #
    @3
    @79
    @28
    @21
    @24
    wss
    #
    wi
    vg
    @28
    vg
    @21
    ssintab
    @28
    @24
    @20
    wcel
    #
    @80
    @28
    @10
    @24
    @34
    wceq
    #
    wa
    #
    vr
    wex
    @81
    @10
    @27
    @82
    vs
    vr
    @77
    @26
    @34
    @24
    @78
    eqeq2d
    rexab2
    @83
    @81
    vr
    @83
    @24
    @34
    @20
    @10
    @82
    simpr
    @83
    cR
    @13
    cima
    #
    @34
    wss
    #
    cR
    @34
    cima
    #
    @34
    wss
    #
    wa
    #
    @34
    @20
    wcel
    @10
    @88
    @82
    @10
    @85
    @87
    @7
    @85
    @9
    cR
    @6
    @13
    imass1
    adantr
    @7
    @9
    @86
    @6
    @34
    cima
    #
    @34
    cR
    @6
    @34
    imass1
    @9
    @89
    @8
    @13
    cima
    @34
    @6
    @6
    @13
    imaco
    @8
    @6
    @13
    imass1
    syl5eqssr
    sylan9ss
    jca
    adantr
    @19
    @88
    vf
    @34
    @6
    cvv
    wcel
    @34
    cvv
    wcel
    vr
    vex
    @6
    @13
    cvv
    imaexg
    ax-mp
    @19
    @84
    @16
    wss
    cR
    @16
    cima
    #
    @16
    wss
    #
    wa
    #
    @35
    @88
    @19
    @84
    @90
    cun
    #
    @16
    wss
    @92
    @18
    @93
    @16
    cR
    @13
    @16
    imaundi
    sseq1i
    @84
    @90
    @16
    unss
    bitr4i
    @91
    @87
    @16
    @34
    @84
    @35
    @90
    @86
    @16
    @34
    @16
    @34
    cR
    imaeq2
    @35
    id
    sseq12d
    cleq2lem
    syl5bb
    elab
    sylibr
    eqeltrd
    exlimiv
    sylbi
    @24
    @20
    intss1
    syl
    mpgbir
    a1i
    eqssd
    eqtrd
    eleq2d
    bitrd
end

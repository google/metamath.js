include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "wf.mm"
include "cfv.mm"
include "wcel.mm"
include "cxp.mm"
include "wss.mm"
include "wa.mm"
include "wral.mm"
include "wex.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "ccmp.mm"
include "cop.mm"
include "csn.mm"
include "adantr.mm"
include "id.mm"
include "snidg.mm"
include "syl.mm"
include "opelxpi.mm"
include "syl2anr.mm"
include "sseldd.mm"
include "ctx.mm"
include "co.mm"
include "ctop.mm"
include "wb.mm"
include "eltx.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "2rexbidv.mm"
include "rspcv.mm"
include "sylc.mm"
include "opelxp.mm"
include "anbi1i.mm"
include "anass.mm"
include "bitri.mm"
include "rexbii.mm"
include "r19.42v.mm"
include "sylib.mm"
include "ralrimiva.mm"
include "eleq2.mm"
include "xpeq2.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "cmpcovf.mm"
include "crn.mm"
include "cint.mm"
include "c0.mm"
include "rint0.mm"
include "adantl.mm"
include "topopn.mm"
include "ad3antrrr.mm"
include "eqeltrd.mm"
include "wne.mm"
include "simprrl.mm"
include "frn.mm"
include "simpr.mm"
include "wfo.mm"
include "inss2.mm"
include "simplr.mm"
include "sseldi.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn4.mm"
include "fofi.mm"
include "w3a.mm"
include "fiinopn.mm"
include "imp.mm"
include "syl13anc.mm"
include "elssuni.mm"
include "syl6sseqr.mm"
include "sseqin2.mm"
include "pm2.61dane.mm"
include "ad2antrr.mm"
include "ciin.mm"
include "simprrr.mm"
include "simpl.mm"
include "ralimi.mm"
include "eliin.mm"
include "mpbird.mm"
include "fniinfv.mm"
include "eleqtrd.mm"
include "elind.mm"
include "ciun.mm"
include "simprl.mm"
include "uniiun.mm"
include "syl6eq.mm"
include "xpeq1d.mm"
include "xpiundir.mm"
include "wi.mm"
include "iinss2.mm"
include "eqsstr3d.mm"
include "syl5ss.mm"
include "xpss2.mm"
include "sstr2.mm"
include "3syl.mm"
include "ralimdva.mm"
include "iunss.mm"
include "sylibr.mm"
include "eqsstrd.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "expr.mm"
include "exlimdv.mm"
include "expimpd.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem txtube
  let wph: wff ph
  let vu: setvar u
  let cA: class A
  let cR: class R
  let cS: class S
  let cU: class U
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vt: setvar t
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  assume txtube.x: |- X = U. R
  assume txtube.y: |- Y = U. S
  assume txtube.r: |- ( ph -> R e. Comp )
  assume txtube.s: |- ( ph -> S e. Top )
  assume txtube.w: |- ( ph -> U e. ( R tX S ) )
  assume txtube.u: |- ( ph -> ( X X. { A } ) C_ U )
  assume txtube.a: |- ( ph -> A e. Y )

  disjoint A u
  disjoint R u
  disjoint S u
  disjoint Y u
  disjoint ph u
  disjoint U u
  disjoint X u
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint A t
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  disjoint A v
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint R f
  disjoint R t
  disjoint R v
  disjoint R x
  disjoint R y
  disjoint S f
  disjoint S t
  disjoint S v
  disjoint S x
  disjoint S y
  disjoint f ph
  disjoint ph t
  disjoint ph v
  disjoint ph x
  disjoint U f
  disjoint U t
  disjoint U v
  disjoint U x
  disjoint U y
  disjoint X f
  disjoint X t
  disjoint X v
  disjoint X x
  assert |- ( ph -> E. u e. S ( A e. u /\ ( X X. u ) C_ U ) )

  proof
    wph
    cX
    vt
    cv
    #
    cuni
    #
    wceq
    #
    @0
    cS
    vf
    cv
    #
    wf
    #
    cA
    vu
    cv
    #
    @3
    cfv
    #
    wcel
    #
    @5
    @6
    cxp
    #
    cU
    wss
    #
    wa
    #
    vu
    @0
    wral
    #
    wa
    #
    vf
    wex
    #
    wa
    #
    vt
    cR
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    cA
    @5
    wcel
    #
    cX
    @5
    cxp
    #
    cU
    wss
    #
    wa
    #
    vu
    cS
    wrex
    #
    wph
    cR
    ccmp
    wcel
    #
    vx
    cv
    #
    @5
    wcel
    #
    cA
    vv
    cv
    #
    wcel
    #
    @5
    @26
    cxp
    #
    cU
    wss
    #
    wa
    #
    vv
    cS
    wrex
    wa
    #
    vu
    cR
    wrex
    #
    vx
    cX
    wral
    @17
    txtube.r
    wph
    @32
    vx
    cX
    wph
    @24
    cX
    wcel
    #
    wa
    #
    @24
    cA
    cop
    #
    @28
    wcel
    #
    @29
    wa
    #
    vv
    cS
    wrex
    #
    vu
    cR
    wrex
    #
    @32
    @34
    @35
    cU
    wcel
    vy
    cv
    #
    @28
    wcel
    #
    @29
    wa
    #
    vv
    cS
    wrex
    vu
    cR
    wrex
    #
    vy
    cU
    wral
    #
    @39
    @34
    cX
    cA
    csn
    #
    cxp
    #
    cU
    @35
    wph
    @46
    cU
    wss
    @33
    txtube.u
    adantr
    @33
    @33
    cA
    @45
    wcel
    #
    @35
    @46
    wcel
    wph
    @33
    id
    wph
    cA
    cY
    wcel
    #
    @47
    txtube.a
    cA
    cY
    snidg
    syl
    @24
    cA
    cX
    @45
    opelxpi
    syl2anr
    sseldd
    wph
    @44
    @33
    wph
    cU
    cR
    cS
    ctx
    co
    wcel
    #
    @44
    txtube.w
    wph
    @23
    cS
    ctop
    wcel
    #
    @49
    @44
    wb
    txtube.r
    txtube.s
    vu
    vv
    cU
    cR
    cS
    ccmp
    ctop
    vy
    eltx
    syl2anc
    mpbid
    adantr
    @43
    @39
    vy
    @35
    cU
    @40
    @35
    wceq
    #
    @42
    @37
    vu
    vv
    cR
    cS
    @51
    @41
    @36
    @29
    @40
    @35
    @28
    eleq1
    anbi1d
    2rexbidv
    rspcv
    sylc
    @38
    @31
    vu
    cR
    @38
    @25
    @30
    wa
    #
    vv
    cS
    wrex
    @31
    @37
    @52
    vv
    cS
    @37
    @25
    @27
    wa
    #
    @29
    wa
    @52
    @36
    @53
    @29
    @24
    cA
    @5
    @26
    opelxp
    anbi1i
    @25
    @27
    @29
    anass
    bitri
    rexbii
    @25
    @30
    vv
    cS
    r19.42v
    bitri
    rexbii
    sylib
    ralrimiva
    @30
    @10
    vx
    vu
    vv
    cS
    vf
    cR
    cX
    vt
    txtube.x
    @26
    @6
    wceq
    #
    @27
    @7
    @29
    @9
    @26
    @6
    cA
    eleq2
    @54
    @28
    @8
    cU
    @26
    @6
    @5
    xpeq2
    sseq1d
    anbi12d
    cmpcovf
    syl2anc
    wph
    @14
    @22
    vt
    @16
    wph
    @0
    @16
    wcel
    #
    wa
    #
    @2
    @13
    @22
    @56
    @2
    wa
    @12
    @22
    vf
    @56
    @2
    @12
    @22
    @56
    @2
    @12
    wa
    #
    wa
    #
    cY
    @3
    crn
    #
    cint
    #
    cin
    #
    cS
    wcel
    #
    cA
    @61
    wcel
    #
    cX
    @61
    cxp
    #
    cU
    wss
    #
    @22
    @58
    @62
    @59
    c0
    @58
    @59
    c0
    wceq
    #
    wa
    @61
    cY
    cS
    @66
    @61
    cY
    wceq
    @58
    cY
    @59
    rint0
    adantl
    wph
    cY
    cS
    wcel
    #
    @55
    @57
    @66
    wph
    @50
    @67
    txtube.s
    cS
    cY
    txtube.y
    topopn
    syl
    ad3antrrr
    eqeltrd
    @58
    @59
    c0
    wne
    #
    wa
    #
    @61
    @60
    cS
    @69
    @60
    cY
    wss
    @61
    @60
    wceq
    @69
    @60
    cS
    cuni
    #
    cY
    @69
    @60
    cS
    wcel
    #
    @60
    @70
    wss
    @69
    @50
    @59
    cS
    wss
    #
    @68
    @59
    cfn
    wcel
    #
    @71
    wph
    @50
    @55
    @57
    @68
    txtube.s
    ad3antrrr
    @58
    @72
    @68
    @58
    @4
    @72
    @56
    @2
    @4
    @11
    simprrl
    #
    @0
    cS
    @3
    frn
    syl
    adantr
    @58
    @68
    simpr
    @58
    @73
    @68
    @58
    @0
    cfn
    wcel
    @0
    @59
    @3
    wfo
    #
    @73
    @58
    @16
    cfn
    @0
    @15
    cfn
    inss2
    wph
    @55
    @57
    simplr
    sseldi
    @58
    @3
    @0
    wfn
    #
    @75
    @58
    @4
    @76
    @74
    @0
    cS
    @3
    ffn
    syl
    #
    @0
    @3
    dffn4
    sylib
    @0
    @59
    @3
    fofi
    syl2anc
    adantr
    @50
    @72
    @68
    @73
    w3a
    @71
    @59
    cS
    fiinopn
    imp
    syl13anc
    #
    @60
    cS
    elssuni
    syl
    txtube.y
    syl6sseqr
    @60
    cY
    sseqin2
    sylib
    @78
    eqeltrd
    pm2.61dane
    @58
    cY
    @60
    cA
    wph
    @48
    @55
    @57
    txtube.a
    ad2antrr
    #
    @58
    cA
    vu
    @0
    @6
    ciin
    #
    @60
    @58
    cA
    @80
    wcel
    #
    @7
    vu
    @0
    wral
    #
    @58
    @11
    @82
    @56
    @2
    @4
    @11
    simprrr
    #
    @10
    @7
    vu
    @0
    @7
    @9
    simpl
    ralimi
    syl
    @58
    @48
    @81
    @82
    wb
    @79
    vu
    cA
    @0
    @6
    cY
    eliin
    syl
    mpbird
    @58
    @76
    @80
    @60
    wceq
    #
    @77
    vu
    @0
    @3
    fniinfv
    #
    syl
    eleqtrd
    elind
    @58
    @64
    vu
    @0
    @5
    @61
    cxp
    #
    ciun
    #
    cU
    @58
    @64
    vu
    @0
    @5
    ciun
    #
    @61
    cxp
    @87
    @58
    cX
    @88
    @61
    @58
    cX
    @1
    @88
    @56
    @2
    @12
    simprl
    vu
    @0
    uniiun
    syl6eq
    xpeq1d
    vu
    @0
    @5
    @61
    xpiundir
    syl6eq
    @58
    @86
    cU
    wss
    #
    vu
    @0
    wral
    #
    @87
    cU
    wss
    @58
    @76
    @9
    vu
    @0
    wral
    #
    @90
    @77
    @58
    @11
    @91
    @83
    @10
    @9
    vu
    @0
    @7
    @9
    simpr
    ralimi
    syl
    @76
    @9
    @89
    vu
    @0
    @76
    @5
    @0
    wcel
    #
    wa
    #
    @61
    @6
    wss
    @86
    @8
    wss
    @9
    @89
    wi
    @93
    @61
    @60
    @6
    cY
    @60
    inss2
    @93
    @60
    @80
    @6
    @76
    @84
    @92
    @85
    adantr
    @92
    @80
    @6
    wss
    @76
    vu
    @0
    @6
    iinss2
    adantl
    eqsstr3d
    syl5ss
    @61
    @6
    @5
    xpss2
    @86
    @8
    cU
    sstr2
    3syl
    ralimdva
    sylc
    vu
    @0
    @86
    cU
    iunss
    sylibr
    eqsstrd
    @21
    @63
    @65
    wa
    vu
    @61
    cS
    @5
    @61
    wceq
    #
    @18
    @63
    @20
    @65
    @5
    @61
    cA
    eleq2
    @94
    @19
    @64
    cU
    @5
    @61
    cX
    xpeq2
    sseq1d
    anbi12d
    rspcev
    syl12anc
    expr
    exlimdv
    expimpd
    rexlimdva
    mpd
end

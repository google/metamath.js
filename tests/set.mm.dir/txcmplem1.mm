include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "wf.mm"
include "csn.mm"
include "cxp.mm"
include "cfv.mm"
include "wss.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wcel.mm"
include "ccmp.mm"
include "cop.mm"
include "id.mm"
include "opelxpi.mm"
include "syl2anr.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "eluni2.mm"
include "sylib.mm"
include "wi.mm"
include "ctx.mm"
include "co.mm"
include "sselda.mm"
include "wb.mm"
include "eltx.mm"
include "syl2anc.mm"
include "biimpa.mm"
include "syldan.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "2rexbidv.mm"
include "rspccv.mm"
include "syl.mm"
include "opelxp1.mm"
include "ad2antrl.mm"
include "opelxp2.mm"
include "snssd.mm"
include "xpss2.mm"
include "simprr.mm"
include "sstrd.mm"
include "jca.mm"
include "ex.mm"
include "rexlimdvw.mm"
include "reximdv.mm"
include "syld.mm"
include "reximdva.mm"
include "mpd.mm"
include "rexcom.mm"
include "r19.42v.mm"
include "rexbii.mm"
include "bitri.mm"
include "ralrimiva.mm"
include "sseq2.mm"
include "cmpcovf.mm"
include "crn.mm"
include "ad2antrr.mm"
include "ctop.mm"
include "cmptop.mm"
include "txtop.mm"
include "simprrl.mm"
include "frn.mm"
include "uniopn.mm"
include "ciun.mm"
include "simprrr.mm"
include "ss2iun.mm"
include "simprl.mm"
include "uniiun.mm"
include "syl6eq.mm"
include "xpeq1d.mm"
include "xpiundir.mm"
include "syl6req.mm"
include "wfn.mm"
include "ffn.mm"
include "fniunfv.mm"
include "3sstr3d.mm"
include "txtube.mm"
include "vex.mm"
include "rnex.mm"
include "elpw.mm"
include "sylibr.mm"
include "wfo.mm"
include "inss2.mm"
include "simplr.mm"
include "sseldi.mm"
include "dffn4.mm"
include "fofi.mm"
include "elind.mm"
include "unieq.mm"
include "sseq2d.mm"
include "rspcev.mm"
include "anim2d.mm"
include "expr.mm"
include "exlimdv.mm"
include "expimpd.mm"
include "rexlimdva.mm"

theorem txcmplem1
  let wph: wff ph
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cR: class R
  let cS: class S
  let cW: class W
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vk: setvar k
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  assume txcmp.x: |- X = U. R
  assume txcmp.y: |- Y = U. S
  assume txcmp.r: |- ( ph -> R e. Comp )
  assume txcmp.s: |- ( ph -> S e. Comp )
  assume txcmp.w: |- ( ph -> W C_ ( R tX S ) )
  assume txcmp.u: |- ( ph -> ( X X. Y ) = U. W )
  assume txcmp.a: |- ( ph -> A e. Y )

  disjoint A u
  disjoint u v
  disjoint S u
  disjoint S v
  disjoint Y u
  disjoint Y v
  disjoint W u
  disjoint W v
  disjoint X u
  disjoint X v
  disjoint ph u
  disjoint R u
  disjoint f k
  disjoint f r
  disjoint f s
  disjoint f t
  disjoint f u
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint k r
  disjoint k s
  disjoint k t
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r x
  disjoint r y
  disjoint A r
  disjoint s t
  disjoint s u
  disjoint s x
  disjoint s y
  disjoint A s
  disjoint t u
  disjoint t x
  disjoint t y
  disjoint A t
  disjoint u x
  disjoint u y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint f v
  disjoint f w
  disjoint f z
  disjoint S f
  disjoint r v
  disjoint r w
  disjoint r z
  disjoint S r
  disjoint s v
  disjoint s w
  disjoint s z
  disjoint S s
  disjoint t v
  disjoint t w
  disjoint t z
  disjoint S t
  disjoint u w
  disjoint u z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint S w
  disjoint x z
  disjoint S x
  disjoint y z
  disjoint S y
  disjoint S z
  disjoint Y f
  disjoint Y w
  disjoint Y x
  disjoint Y z
  disjoint W f
  disjoint k v
  disjoint k w
  disjoint k z
  disjoint W k
  disjoint W r
  disjoint W s
  disjoint W t
  disjoint W w
  disjoint W x
  disjoint W z
  disjoint X f
  disjoint X k
  disjoint X r
  disjoint X s
  disjoint X t
  disjoint X w
  disjoint X x
  disjoint X z
  disjoint f ph
  disjoint k ph
  disjoint ph r
  disjoint ph s
  disjoint ph t
  disjoint ph w
  disjoint ph x
  disjoint ph z
  disjoint R f
  disjoint R k
  disjoint R r
  disjoint R s
  disjoint R t
  disjoint R x
  disjoint R y
  assert |- ( ph -> E. u e. S ( A e. u /\ E. v e. ( ~P W i^i Fin ) ( X X. u ) C_ U. v ) )

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
    cW
    vf
    cv
    #
    wf
    #
    vr
    cv
    #
    cA
    csn
    #
    cxp
    #
    @5
    @3
    cfv
    #
    wss
    #
    vr
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
    vu
    cv
    #
    wcel
    #
    cX
    @17
    cxp
    #
    vv
    cv
    #
    cuni
    #
    wss
    #
    vv
    cW
    cpw
    #
    cfn
    cin
    #
    wrex
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
    @7
    vk
    cv
    #
    wss
    #
    vk
    cW
    wrex
    wa
    #
    vr
    cR
    wrex
    #
    vx
    cX
    wral
    @16
    txcmp.r
    wph
    @34
    vx
    cX
    wph
    @29
    cX
    wcel
    #
    wa
    #
    @30
    @32
    wa
    #
    vr
    cR
    wrex
    #
    vk
    cW
    wrex
    #
    @34
    @36
    @29
    cA
    cop
    #
    @31
    wcel
    #
    vk
    cW
    wrex
    #
    @39
    @36
    @40
    cW
    cuni
    #
    wcel
    @42
    @36
    @40
    cX
    cY
    cxp
    #
    @43
    @35
    @35
    cA
    cY
    wcel
    #
    @40
    @44
    wcel
    wph
    @35
    id
    txcmp.a
    @29
    cA
    cX
    cY
    opelxpi
    syl2anr
    wph
    @44
    @43
    wceq
    @35
    txcmp.u
    adantr
    eleqtrd
    vk
    @40
    cW
    eluni2
    sylib
    @36
    @41
    @38
    vk
    cW
    @36
    @31
    cW
    wcel
    #
    wa
    #
    @41
    @40
    @5
    vs
    cv
    #
    cxp
    #
    wcel
    #
    @49
    @31
    wss
    #
    wa
    #
    vs
    cS
    wrex
    #
    vr
    cR
    wrex
    #
    @38
    @47
    vy
    cv
    #
    @49
    wcel
    #
    @51
    wa
    #
    vs
    cS
    wrex
    vr
    cR
    wrex
    #
    vy
    @31
    wral
    #
    @41
    @54
    wi
    @36
    @46
    @31
    cR
    cS
    ctx
    co
    #
    wcel
    #
    @59
    @36
    cW
    @60
    @31
    wph
    cW
    @60
    wss
    #
    @35
    txcmp.w
    adantr
    sselda
    @36
    @61
    @59
    wph
    @61
    @59
    wb
    #
    @35
    wph
    @28
    cS
    ccmp
    wcel
    #
    @63
    txcmp.r
    txcmp.s
    vr
    vs
    @31
    cR
    cS
    ccmp
    ccmp
    vy
    eltx
    syl2anc
    adantr
    biimpa
    syldan
    @58
    @54
    vy
    @40
    @31
    @55
    @40
    wceq
    #
    @57
    @52
    vr
    vs
    cR
    cS
    @65
    @56
    @50
    @51
    @55
    @40
    @49
    eleq1
    anbi1d
    2rexbidv
    rspccv
    syl
    @47
    @53
    @37
    vr
    cR
    @47
    @52
    @37
    vs
    cS
    @47
    @52
    @37
    @47
    @52
    wa
    #
    @30
    @32
    @50
    @30
    @47
    @51
    @29
    cA
    @5
    @48
    opelxp1
    ad2antrl
    @66
    @7
    @49
    @31
    @66
    @6
    @48
    wss
    @7
    @49
    wss
    @66
    cA
    @48
    @50
    cA
    @48
    wcel
    @47
    @51
    @29
    cA
    @5
    @48
    opelxp2
    ad2antrl
    snssd
    @6
    @48
    @5
    xpss2
    syl
    @47
    @50
    @51
    simprr
    sstrd
    jca
    ex
    rexlimdvw
    reximdv
    syld
    reximdva
    mpd
    @39
    @37
    vk
    cW
    wrex
    #
    vr
    cR
    wrex
    @34
    @37
    vk
    vr
    cW
    cR
    rexcom
    @67
    @33
    vr
    cR
    @30
    @32
    vk
    cW
    r19.42v
    rexbii
    bitri
    sylib
    ralrimiva
    @32
    @9
    vx
    vr
    vk
    cW
    vf
    cR
    cX
    vt
    txcmp.x
    @31
    @8
    @7
    sseq2
    cmpcovf
    syl2anc
    wph
    @13
    @27
    vt
    @15
    wph
    @0
    @15
    wcel
    #
    wa
    #
    @2
    @12
    @27
    @69
    @2
    wa
    @11
    @27
    vf
    @69
    @2
    @11
    @27
    @69
    @2
    @11
    wa
    #
    wa
    #
    @18
    @19
    @3
    crn
    #
    cuni
    #
    wss
    #
    wa
    #
    vu
    cS
    wrex
    @27
    @71
    vu
    cA
    cR
    cS
    @73
    cX
    cY
    txcmp.x
    txcmp.y
    wph
    @28
    @68
    @70
    txcmp.r
    ad2antrr
    #
    wph
    cS
    ctop
    wcel
    #
    @68
    @70
    wph
    @64
    @77
    txcmp.s
    cS
    cmptop
    syl
    ad2antrr
    #
    @71
    @60
    ctop
    wcel
    #
    @72
    @60
    wss
    @73
    @60
    wcel
    @71
    cR
    ctop
    wcel
    #
    @77
    @79
    @71
    @28
    @80
    @76
    cR
    cmptop
    syl
    @78
    cR
    cS
    txtop
    syl2anc
    @71
    @72
    cW
    @60
    @71
    @4
    @72
    cW
    wss
    #
    @69
    @2
    @4
    @10
    simprrl
    #
    @0
    cW
    @3
    frn
    syl
    #
    wph
    @62
    @68
    @70
    txcmp.w
    ad2antrr
    sstrd
    @72
    @60
    uniopn
    syl2anc
    @71
    vr
    @0
    @7
    ciun
    #
    vr
    @0
    @8
    ciun
    #
    cX
    @6
    cxp
    #
    @73
    @71
    @10
    @84
    @85
    wss
    @69
    @2
    @4
    @10
    simprrr
    vr
    @0
    @7
    @8
    ss2iun
    syl
    @71
    @86
    vr
    @0
    @5
    ciun
    #
    @6
    cxp
    @84
    @71
    cX
    @87
    @6
    @71
    cX
    @1
    @87
    @69
    @2
    @11
    simprl
    vr
    @0
    uniiun
    syl6eq
    xpeq1d
    vr
    @0
    @5
    @6
    xpiundir
    syl6req
    @71
    @3
    @0
    wfn
    #
    @85
    @73
    wceq
    @71
    @4
    @88
    @82
    @0
    cW
    @3
    ffn
    syl
    #
    vr
    @0
    @3
    fniunfv
    syl
    3sstr3d
    wph
    @45
    @68
    @70
    txcmp.a
    ad2antrr
    txtube
    @71
    @75
    @26
    vu
    cS
    @71
    @74
    @25
    @18
    @71
    @72
    @24
    wcel
    #
    @74
    @25
    wi
    @71
    @23
    cfn
    @72
    @71
    @81
    @72
    @23
    wcel
    @83
    @72
    cW
    @3
    vf
    vex
    rnex
    elpw
    sylibr
    @71
    @0
    cfn
    wcel
    @0
    @72
    @3
    wfo
    #
    @72
    cfn
    wcel
    @71
    @15
    cfn
    @0
    @14
    cfn
    inss2
    wph
    @68
    @70
    simplr
    sseldi
    @71
    @88
    @91
    @89
    @0
    @3
    dffn4
    sylib
    @0
    @72
    @3
    fofi
    syl2anc
    elind
    @90
    @74
    @25
    @22
    @74
    vv
    @72
    @24
    @20
    @72
    wceq
    @21
    @73
    @19
    @20
    @72
    unieq
    sseq2d
    rspcev
    ex
    syl
    anim2d
    reximdv
    mpd
    expr
    exlimdv
    expimpd
    rexlimdva
    mpd
end

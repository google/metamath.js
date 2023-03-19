include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wf.mm"
include "cxp.mm"
include "cfv.mm"
include "wss.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "ccmp.mm"
include "wcel.mm"
include "adantr.mm"
include "ctx.mm"
include "co.mm"
include "simpr.mm"
include "txcmplem1.mm"
include "ralrimiva.mm"
include "unieq.mm"
include "sseq2d.mm"
include "cmpcovf.mm"
include "syl2anc.mm"
include "ciun.mm"
include "crn.mm"
include "wfn.mm"
include "simprrl.mm"
include "ffn.mm"
include "fniunfv.mm"
include "3syl.mm"
include "frn.mm"
include "syl.mm"
include "inss1.mm"
include "syl6ss.mm"
include "sspwuni.mm"
include "sylib.mm"
include "eqsstrd.mm"
include "vex.mm"
include "fvex.mm"
include "iunex.mm"
include "elpw.mm"
include "sylibr.mm"
include "inss2.mm"
include "simplr.mm"
include "sseldi.mm"
include "fss.mm"
include "sylancl.mm"
include "ffvelrn.mm"
include "iunfi.mm"
include "elind.mm"
include "simprl.mm"
include "uniiun.mm"
include "syl6eq.mm"
include "xpeq2d.mm"
include "xpiundi.mm"
include "simprrr.mm"
include "xpeq2.mm"
include "fveq2.mm"
include "unieqd.mm"
include "sseq12d.mm"
include "cbvralv.mm"
include "ss2iun.mm"
include "ffvelrnda.mm"
include "elpwi.mm"
include "uniss.mm"
include "ad3antrrr.mm"
include "sseqtr4d.mm"
include "iunss.mm"
include "eqssd.mm"
include "iuncom4.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "expr.mm"
include "exlimdv.mm"
include "expimpd.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem txcmplem2
  let wph: wff ph
  let vv: setvar v
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
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vw: setvar w
  let vz: setvar z
  assume txcmp.x: |- X = U. R
  assume txcmp.y: |- Y = U. S
  assume txcmp.r: |- ( ph -> R e. Comp )
  assume txcmp.s: |- ( ph -> S e. Comp )
  assume txcmp.w: |- ( ph -> W C_ ( R tX S ) )
  assume txcmp.u: |- ( ph -> ( X X. Y ) = U. W )

  disjoint S v
  disjoint Y v
  disjoint W v
  disjoint X v
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
  disjoint A u
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
  disjoint u v
  disjoint u w
  disjoint u z
  disjoint S u
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
  disjoint Y u
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
  disjoint W u
  disjoint W w
  disjoint W x
  disjoint W z
  disjoint X f
  disjoint X k
  disjoint X r
  disjoint X s
  disjoint X t
  disjoint X u
  disjoint X w
  disjoint X x
  disjoint X z
  disjoint f ph
  disjoint k ph
  disjoint ph r
  disjoint ph s
  disjoint ph t
  disjoint ph u
  disjoint ph w
  disjoint ph x
  disjoint ph z
  disjoint R f
  disjoint R k
  disjoint R r
  disjoint R s
  disjoint R t
  disjoint R u
  disjoint R x
  disjoint R y
  assert |- ( ph -> E. v e. ( ~P W i^i Fin ) ( X X. Y ) = U. v )

  proof
    wph
    cY
    vw
    cv
    #
    cuni
    #
    wceq
    #
    @0
    cW
    cpw
    #
    cfn
    cin
    #
    vf
    cv
    #
    wf
    #
    cX
    vu
    cv
    #
    cxp
    #
    @7
    @5
    cfv
    #
    cuni
    #
    wss
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
    vw
    cS
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    cX
    cY
    cxp
    #
    vv
    cv
    #
    cuni
    #
    wceq
    #
    vv
    @4
    wrex
    #
    wph
    cS
    ccmp
    wcel
    #
    vx
    cv
    #
    @7
    wcel
    @8
    @21
    wss
    #
    vv
    @4
    wrex
    wa
    vu
    cS
    wrex
    #
    vx
    cY
    wral
    @18
    txcmp.s
    wph
    @27
    vx
    cY
    wph
    @25
    cY
    wcel
    #
    wa
    vv
    vu
    @25
    cR
    cS
    cW
    cX
    cY
    txcmp.x
    txcmp.y
    wph
    cR
    ccmp
    wcel
    @28
    txcmp.r
    adantr
    wph
    @24
    @28
    txcmp.s
    adantr
    wph
    cW
    cR
    cS
    ctx
    co
    wss
    @28
    txcmp.w
    adantr
    wph
    @19
    cW
    cuni
    #
    wceq
    #
    @28
    txcmp.u
    adantr
    wph
    @28
    simpr
    txcmplem1
    ralrimiva
    @26
    @11
    vx
    vu
    vv
    @4
    vf
    cS
    cY
    vw
    txcmp.y
    @20
    @9
    wceq
    @21
    @10
    @8
    @20
    @9
    unieq
    sseq2d
    cmpcovf
    syl2anc
    wph
    @15
    @23
    vw
    @17
    wph
    @0
    @17
    wcel
    #
    wa
    #
    @2
    @14
    @23
    @32
    @2
    wa
    @13
    @23
    vf
    @32
    @2
    @13
    @23
    @32
    @2
    @13
    wa
    #
    wa
    #
    vz
    @0
    vz
    cv
    #
    @5
    cfv
    #
    ciun
    #
    @4
    wcel
    @19
    @37
    cuni
    #
    wceq
    #
    @23
    @34
    @3
    cfn
    @37
    @34
    @37
    cW
    wss
    @37
    @3
    wcel
    @34
    @37
    @5
    crn
    #
    cuni
    #
    cW
    @34
    @6
    @5
    @0
    wfn
    @37
    @41
    wceq
    @32
    @2
    @6
    @12
    simprrl
    #
    @0
    @4
    @5
    ffn
    vz
    @0
    @5
    fniunfv
    3syl
    @34
    @40
    @3
    wss
    @41
    cW
    wss
    @34
    @40
    @4
    @3
    @34
    @6
    @40
    @4
    wss
    @42
    @0
    @4
    @5
    frn
    syl
    @3
    cfn
    inss1
    #
    syl6ss
    @40
    cW
    sspwuni
    sylib
    eqsstrd
    @37
    cW
    vz
    @0
    @36
    vw
    vex
    @35
    @5
    fvex
    iunex
    elpw
    sylibr
    @34
    @0
    cfn
    wcel
    @36
    cfn
    wcel
    #
    vz
    @0
    wral
    #
    @37
    cfn
    wcel
    @34
    @17
    cfn
    @0
    @16
    cfn
    inss2
    wph
    @31
    @33
    simplr
    sseldi
    @34
    @0
    cfn
    @5
    wf
    #
    @45
    @34
    @6
    @4
    cfn
    wss
    @46
    @42
    @3
    cfn
    inss2
    @0
    @4
    cfn
    @5
    fss
    sylancl
    @46
    @44
    vz
    @0
    @0
    cfn
    @35
    @5
    ffvelrn
    ralrimiva
    syl
    vz
    @0
    @36
    iunfi
    syl2anc
    elind
    @34
    @19
    vz
    @0
    @36
    cuni
    #
    ciun
    #
    @38
    @34
    @19
    @48
    @34
    @19
    vz
    @0
    cX
    @35
    cxp
    #
    ciun
    #
    @48
    @34
    @19
    cX
    vz
    @0
    @35
    ciun
    #
    cxp
    @50
    @34
    cY
    @51
    cX
    @34
    cY
    @1
    @51
    @32
    @2
    @13
    simprl
    vz
    @0
    uniiun
    syl6eq
    xpeq2d
    vz
    @0
    @35
    cX
    xpiundi
    syl6eq
    @34
    @49
    @47
    wss
    #
    vz
    @0
    wral
    #
    @50
    @48
    wss
    @34
    @12
    @53
    @32
    @2
    @6
    @12
    simprrr
    @11
    @52
    vu
    vz
    @0
    @7
    @35
    wceq
    #
    @8
    @49
    @10
    @47
    @7
    @35
    cX
    xpeq2
    @54
    @9
    @36
    @7
    @35
    @5
    fveq2
    unieqd
    sseq12d
    cbvralv
    sylib
    vz
    @0
    @49
    @47
    ss2iun
    syl
    eqsstrd
    @34
    @47
    @19
    wss
    #
    vz
    @0
    wral
    @48
    @19
    wss
    @34
    @55
    vz
    @0
    @34
    @35
    @0
    wcel
    #
    wa
    #
    @47
    @29
    @19
    @57
    @36
    @3
    wcel
    @36
    cW
    wss
    @47
    @29
    wss
    @57
    @4
    @3
    @36
    @43
    @34
    @0
    @4
    @35
    @5
    @42
    ffvelrnda
    sseldi
    @36
    cW
    elpwi
    @36
    cW
    uniss
    3syl
    wph
    @30
    @31
    @33
    @56
    txcmp.u
    ad3antrrr
    sseqtr4d
    ralrimiva
    vz
    @0
    @47
    @19
    iunss
    sylibr
    eqssd
    vz
    @0
    @36
    iuncom4
    syl6eq
    @22
    @39
    vv
    @37
    @4
    @20
    @37
    wceq
    @21
    @38
    @19
    @20
    @37
    unieq
    eqeq2d
    rspcev
    syl2anc
    expr
    exlimdv
    expimpd
    rexlimdva
    mpd
end

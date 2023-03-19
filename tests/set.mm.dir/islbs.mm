include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "wn.mm"
include "wral.mm"
include "wa.mm"
include "cpw.mm"
include "crab.mm"
include "wss.mm"
include "w3a.mm"
include "cvv.mm"
include "elex.mm"
include "clbs.mm"
include "cbs.mm"
include "cvsca.mm"
include "c0g.mm"
include "csca.mm"
include "wsbc.mm"
include "clspn.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "pweqd.mm"
include "fvexd.mm"
include "adantr.mm"
include "simplr.mm"
include "fveq1d.mm"
include "ad2antrr.mm"
include "eqeq12d.mm"
include "simpr.mm"
include "fveq2d.mm"
include "sneqd.mm"
include "difeq12d.mm"
include "oveqd.mm"
include "eleq12d.mm"
include "notbid.mm"
include "raleqbidv.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "sbcied2.mm"
include "rabeqbidv.mm"
include "df-lbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "pwex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"
include "eleq2d.mm"
include "elpw2.mm"
include "anbi1i.mm"
include "eqeq1d.mm"
include "difeq1.mm"
include "raleqbi1dv.mm"
include "elrab.mm"
include "3anass.mm"
include "3bitr4i.mm"
include "syl6bb.mm"

theorem islbs
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.x: class .x.
  let cF: class F
  let cJ: class J
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vb: setvar b
  let vf: setvar f
  let vn: setvar n
  let vw: setvar w
  assume islbs.v: |- V = ( Base ` W )
  assume islbs.f: |- F = ( Scalar ` W )
  assume islbs.s: |- .x. = ( .s ` W )
  assume islbs.k: |- K = ( Base ` F )
  assume islbs.j: |- J = ( LBasis ` W )
  assume islbs.n: |- N = ( LSpan ` W )
  assume islbs.z: |- .0. = ( 0g ` F )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K y
  disjoint N x
  disjoint N y
  disjoint W x
  disjoint W y
  disjoint F x
  disjoint F y
  disjoint .0. y
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint b f
  disjoint b n
  disjoint b w
  disjoint K b
  disjoint f n
  disjoint f w
  disjoint f y
  disjoint K f
  disjoint n w
  disjoint n y
  disjoint K n
  disjoint w y
  disjoint K w
  disjoint N b
  disjoint f x
  disjoint N f
  disjoint n x
  disjoint N n
  disjoint w x
  disjoint N w
  disjoint W b
  disjoint W f
  disjoint W n
  disjoint W w
  disjoint .x. b
  disjoint .x. f
  disjoint .x. n
  disjoint .x. w
  disjoint V b
  disjoint V f
  disjoint V n
  disjoint V w
  disjoint .0. b
  disjoint .0. f
  disjoint .0. n
  disjoint .0. w
  assert |- ( W e. X -> ( B e. J <-> ( B C_ V /\ ( N ` B ) = V /\ A. x e. B A. y e. ( K \ { .0. } ) -. ( y .x. x ) e. ( N ` ( B \ { x } ) ) ) ) )

  proof
    cW
    cX
    wcel
    #
    cB
    cJ
    wcel
    cB
    vb
    cv
    #
    cN
    cfv
    #
    cV
    wceq
    #
    vy
    cv
    #
    vx
    cv
    #
    c.x
    co
    #
    @1
    @5
    csn
    #
    cdif
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    vy
    cK
    c.0
    csn
    #
    cdif
    #
    wral
    #
    vx
    @1
    wral
    #
    wa
    #
    vb
    cV
    cpw
    #
    crab
    #
    wcel
    #
    cB
    cV
    wss
    #
    cB
    cN
    cfv
    #
    cV
    wceq
    #
    @6
    cB
    @7
    cdif
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    vy
    @13
    wral
    #
    vx
    cB
    wral
    #
    w3a
    #
    @0
    cJ
    @18
    cB
    @0
    cW
    cvv
    wcel
    #
    cJ
    @18
    wceq
    cW
    cX
    elex
    @30
    cJ
    cW
    clbs
    cfv
    @18
    islbs.j
    vw
    cW
    @1
    vn
    cv
    #
    cfv
    #
    vw
    cv
    #
    cbs
    cfv
    #
    wceq
    #
    @4
    @5
    @33
    cvsca
    cfv
    #
    co
    #
    @8
    @31
    cfv
    #
    wcel
    #
    wn
    #
    vy
    vf
    cv
    #
    cbs
    cfv
    #
    @41
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    wral
    #
    vx
    @1
    wral
    #
    wa
    #
    vf
    @33
    csca
    cfv
    #
    wsbc
    #
    vn
    @33
    clspn
    cfv
    #
    wsbc
    #
    vb
    @34
    cpw
    #
    crab
    @18
    cvv
    clbs
    @33
    cW
    wceq
    #
    @52
    @16
    vb
    @53
    @17
    @54
    @34
    cV
    @54
    @34
    cW
    cbs
    cfv
    #
    cV
    @33
    cW
    cbs
    fveq2
    islbs.v
    syl6eqr
    #
    pweqd
    @54
    @50
    @16
    vn
    @51
    cN
    cvv
    @54
    @33
    clspn
    fvexd
    @54
    @51
    cW
    clspn
    cfv
    cN
    @33
    cW
    clspn
    fveq2
    islbs.n
    syl6eqr
    @54
    @31
    cN
    wceq
    #
    wa
    #
    @48
    @16
    vf
    @49
    cF
    cvv
    @58
    @33
    csca
    fvexd
    @58
    @49
    cW
    csca
    cfv
    #
    cF
    @54
    @49
    @59
    wceq
    @57
    @33
    cW
    csca
    fveq2
    adantr
    islbs.f
    syl6eqr
    @58
    @41
    cF
    wceq
    #
    wa
    #
    @35
    @3
    @47
    @15
    @61
    @32
    @2
    @34
    cV
    @61
    @1
    @31
    cN
    @54
    @57
    @60
    simplr
    #
    fveq1d
    @54
    @34
    cV
    wceq
    @57
    @60
    @56
    ad2antrr
    eqeq12d
    @61
    @46
    @14
    vx
    @1
    @61
    @40
    @11
    vy
    @45
    @13
    @61
    @42
    cK
    @44
    @12
    @61
    @42
    cF
    cbs
    cfv
    cK
    @61
    @41
    cF
    cbs
    @58
    @60
    simpr
    #
    fveq2d
    islbs.k
    syl6eqr
    @61
    @43
    c.0
    @61
    @43
    cF
    c0g
    cfv
    c.0
    @61
    @41
    cF
    c0g
    @63
    fveq2d
    islbs.z
    syl6eqr
    sneqd
    difeq12d
    @61
    @39
    @10
    @61
    @37
    @6
    @38
    @9
    @61
    @36
    c.x
    @4
    @5
    @54
    @36
    c.x
    wceq
    @57
    @60
    @54
    @36
    cW
    cvsca
    cfv
    c.x
    @33
    cW
    cvsca
    fveq2
    islbs.s
    syl6eqr
    ad2antrr
    oveqd
    @61
    @8
    @31
    cN
    @62
    fveq1d
    eleq12d
    notbid
    raleqbidv
    ralbidv
    anbi12d
    sbcied2
    sbcied2
    rabeqbidv
    vx
    vy
    vw
    vn
    vf
    vb
    df-lbs
    @16
    vb
    @17
    cV
    cV
    @55
    cvv
    islbs.v
    cW
    cbs
    fvex
    eqeltri
    #
    pwex
    rabex
    fvmpt
    syl5eq
    syl
    eleq2d
    cB
    @17
    wcel
    #
    @22
    @28
    wa
    #
    wa
    @20
    @66
    wa
    @19
    @29
    @65
    @20
    @66
    cB
    cV
    @64
    elpw2
    anbi1i
    @16
    @66
    vb
    cB
    @17
    @1
    cB
    wceq
    #
    @3
    @22
    @15
    @28
    @67
    @2
    @21
    cV
    @1
    cB
    cN
    fveq2
    eqeq1d
    @14
    @27
    vx
    @1
    cB
    @67
    @11
    @26
    vy
    @13
    @67
    @10
    @25
    @67
    @9
    @24
    @6
    @67
    @8
    @23
    cN
    @1
    cB
    @7
    difeq1
    fveq2d
    eleq2d
    notbid
    ralbidv
    raleqbi1dv
    anbi12d
    elrab
    @20
    @22
    @28
    3anass
    3bitr4i
    syl6bb
end

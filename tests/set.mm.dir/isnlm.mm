include "cngp.mm"
include "clmod.mm"
include "cin.mm"
include "wcel.mm"
include "cnrg.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "cmul.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "cnlm.mm"
include "anass.mm"
include "df-3an.mm"
include "elin.mm"
include "anbi1i.mm"
include "bitr4i.mm"
include "cvsca.mm"
include "cnm.mm"
include "cbs.mm"
include "csca.mm"
include "wsbc.mm"
include "cvv.mm"
include "fvexd.mm"
include "id.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "sylan9eqr.mm"
include "eleq1d.mm"
include "fveq2d.mm"
include "simpl.mm"
include "oveqd.mm"
include "fveq12d.mm"
include "fveq1d.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "sbcied.mm"
include "df-nlm.mm"
include "elrab2.mm"
include "3bitr4ri.mm"

theorem isnlm
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vw: setvar w
  let cX: class X
  let cY: class Y
  assume isnlm.v: |- V = ( Base ` W )
  assume isnlm.n: |- N = ( norm ` W )
  assume isnlm.s: |- .x. = ( .s ` W )
  assume isnlm.f: |- F = ( Scalar ` W )
  assume isnlm.k: |- K = ( Base ` F )
  assume isnlm.a: |- A = ( norm ` F )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint N x
  disjoint N y
  disjoint V x
  disjoint V y
  disjoint K x
  disjoint W x
  disjoint W y
  disjoint .x. x
  disjoint .x. y
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint F f
  disjoint F w
  disjoint N f
  disjoint N w
  disjoint V f
  disjoint V w
  disjoint X x
  disjoint X y
  disjoint K f
  disjoint K w
  disjoint W f
  disjoint W w
  disjoint .x. f
  disjoint .x. w
  disjoint Y y
  assert |- ( W e. NrmMod <-> ( ( W e. NrmGrp /\ W e. LMod /\ F e. NrmRing ) /\ A. x e. K A. y e. V ( N ` ( x .x. y ) ) = ( ( A ` x ) x. ( N ` y ) ) ) )

  proof
    cW
    cngp
    clmod
    cin
    #
    wcel
    #
    cF
    cnrg
    wcel
    #
    wa
    #
    vx
    cv
    #
    vy
    cv
    #
    c.x
    co
    #
    cN
    cfv
    #
    @4
    cA
    cfv
    #
    @5
    cN
    cfv
    #
    cmul
    co
    #
    wceq
    #
    vy
    cV
    wral
    #
    vx
    cK
    wral
    #
    wa
    @1
    @2
    @13
    wa
    #
    wa
    cW
    cngp
    wcel
    #
    cW
    clmod
    wcel
    #
    @2
    w3a
    #
    @13
    wa
    cW
    cnlm
    wcel
    @1
    @2
    @13
    anass
    @17
    @3
    @13
    @17
    @15
    @16
    wa
    #
    @2
    wa
    @3
    @15
    @16
    @2
    df-3an
    @1
    @18
    @2
    cW
    cngp
    clmod
    elin
    anbi1i
    bitr4i
    anbi1i
    vf
    cv
    #
    cnrg
    wcel
    #
    @4
    @5
    vw
    cv
    #
    cvsca
    cfv
    #
    co
    #
    @21
    cnm
    cfv
    #
    cfv
    #
    @4
    @19
    cnm
    cfv
    #
    cfv
    #
    @5
    @24
    cfv
    #
    cmul
    co
    #
    wceq
    #
    vy
    @21
    cbs
    cfv
    #
    wral
    #
    vx
    @19
    cbs
    cfv
    #
    wral
    #
    wa
    #
    vf
    @21
    csca
    cfv
    #
    wsbc
    @14
    vw
    cW
    @0
    cnlm
    @21
    cW
    wceq
    #
    @35
    @14
    vf
    @36
    cvv
    @37
    @21
    csca
    fvexd
    @37
    @19
    @36
    wceq
    #
    wa
    #
    @20
    @2
    @34
    @13
    @39
    @19
    cF
    cnrg
    @38
    @37
    @19
    @36
    cF
    @38
    id
    @37
    @36
    cW
    csca
    cfv
    cF
    @21
    cW
    csca
    fveq2
    isnlm.f
    syl6eqr
    sylan9eqr
    #
    eleq1d
    @39
    @32
    @12
    vx
    @33
    cK
    @39
    @33
    cF
    cbs
    cfv
    cK
    @39
    @19
    cF
    cbs
    @40
    fveq2d
    isnlm.k
    syl6eqr
    @39
    @30
    @11
    vy
    @31
    cV
    @39
    @31
    cW
    cbs
    cfv
    cV
    @39
    @21
    cW
    cbs
    @37
    @38
    simpl
    #
    fveq2d
    isnlm.v
    syl6eqr
    @39
    @25
    @7
    @29
    @10
    @39
    @23
    @6
    @24
    cN
    @39
    @24
    cW
    cnm
    cfv
    cN
    @39
    @21
    cW
    cnm
    @41
    fveq2d
    isnlm.n
    syl6eqr
    #
    @39
    @22
    c.x
    @4
    @5
    @39
    @22
    cW
    cvsca
    cfv
    c.x
    @39
    @21
    cW
    cvsca
    @41
    fveq2d
    isnlm.s
    syl6eqr
    oveqd
    fveq12d
    @39
    @27
    @8
    @28
    @9
    cmul
    @39
    @4
    @26
    cA
    @39
    @26
    cF
    cnm
    cfv
    cA
    @39
    @19
    cF
    cnm
    @40
    fveq2d
    isnlm.a
    syl6eqr
    fveq1d
    @39
    @5
    @24
    cN
    @42
    fveq1d
    oveq12d
    eqeq12d
    raleqbidv
    raleqbidv
    anbi12d
    sbcied
    vx
    vy
    vw
    vf
    df-nlm
    elrab2
    3bitr4ri
end

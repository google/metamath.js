include "clmhm.mm"
include "co.mm"
include "wcel.mm"
include "clmod.mm"
include "wa.mm"
include "cghm.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "w3a.mm"
include "csca.mm"
include "cvsca.mm"
include "cbs.mm"
include "wsbc.mm"
include "crab.mm"
include "df-lmhm.mm"
include "elmpt2cl.mm"
include "oveq12.mm"
include "cvv.mm"
include "fvexd.mm"
include "simplr.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "simpr.mm"
include "simpll.mm"
include "eqtrd.mm"
include "eqeq12d.mm"
include "oveqd.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "sbcied.mm"
include "rabeqbidv.mm"
include "ovex.mm"
include "rabex.mm"
include "ovmpt2a.mm"
include "eleq2d.mm"
include "fveq1.mm"
include "oveq2d.mm"
include "2ralbidv.mm"
include "anbi2d.mm"
include "elrab.mm"
include "3anass.mm"
include "bitr4i.mm"
include "syl6bb.mm"
include "biadan2.mm"

theorem islmhm
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cS: class S
  let cT: class T
  let c.x: class .x.
  let c.xp: class .X.
  let cE: class E
  let cF: class F
  let cK: class K
  let cL: class L
  let vf: setvar f
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let vg: setvar g
  assume islmhm.k: |- K = ( Scalar ` S )
  assume islmhm.l: |- L = ( Scalar ` T )
  assume islmhm.b: |- B = ( Base ` K )
  assume islmhm.e: |- E = ( Base ` S )
  assume islmhm.m: |- .x. = ( .s ` S )
  assume islmhm.n: |- .X. = ( .s ` T )

  disjoint B x
  disjoint E y
  disjoint x y
  disjoint S x
  disjoint S y
  disjoint F x
  disjoint F y
  disjoint T x
  disjoint T y
  disjoint f s
  disjoint f t
  disjoint f w
  disjoint f x
  disjoint B f
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint B s
  disjoint t w
  disjoint t x
  disjoint B t
  disjoint w x
  disjoint B w
  disjoint f y
  disjoint E f
  disjoint s y
  disjoint E s
  disjoint t y
  disjoint E t
  disjoint w y
  disjoint E w
  disjoint K f
  disjoint K s
  disjoint K t
  disjoint K w
  disjoint S f
  disjoint S s
  disjoint S t
  disjoint S w
  disjoint F f
  disjoint f g
  disjoint T f
  disjoint g s
  disjoint g t
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint T g
  disjoint T s
  disjoint T t
  disjoint T w
  disjoint .x. f
  disjoint .x. s
  disjoint .x. t
  disjoint .x. w
  disjoint .X. f
  disjoint .X. s
  disjoint .X. t
  disjoint .X. w
  disjoint L f
  disjoint L s
  disjoint L t
  disjoint L w
  assert |- ( F e. ( S LMHom T ) <-> ( ( S e. LMod /\ T e. LMod ) /\ ( F e. ( S GrpHom T ) /\ L = K /\ A. x e. B A. y e. E ( F ` ( x .x. y ) ) = ( x .X. ( F ` y ) ) ) ) )

  proof
    cF
    cS
    cT
    clmhm
    co
    #
    wcel
    #
    cS
    clmod
    wcel
    cT
    clmod
    wcel
    wa
    #
    cF
    cS
    cT
    cghm
    co
    #
    wcel
    #
    cL
    cK
    wceq
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
    cF
    cfv
    #
    @6
    @7
    cF
    cfv
    #
    c.xp
    co
    #
    wceq
    #
    vy
    cE
    wral
    vx
    cB
    wral
    #
    w3a
    #
    vs
    vt
    clmod
    clmod
    vt
    cv
    #
    csca
    cfv
    #
    vw
    cv
    #
    wceq
    #
    @6
    @7
    vs
    cv
    #
    cvsca
    cfv
    #
    co
    #
    vf
    cv
    #
    cfv
    #
    @6
    @7
    @22
    cfv
    #
    @15
    cvsca
    cfv
    #
    co
    #
    wceq
    #
    vy
    @19
    cbs
    cfv
    #
    wral
    #
    vx
    @17
    cbs
    cfv
    #
    wral
    #
    wa
    #
    vw
    @19
    csca
    cfv
    #
    wsbc
    #
    vf
    @19
    @15
    cghm
    co
    #
    crab
    #
    cS
    cT
    clmhm
    cF
    vx
    vy
    vw
    vt
    vf
    vs
    df-lmhm
    #
    elmpt2cl
    @2
    @1
    cF
    @5
    @8
    @22
    cfv
    #
    @6
    @24
    c.xp
    co
    #
    wceq
    #
    vy
    cE
    wral
    #
    vx
    cB
    wral
    #
    wa
    #
    vf
    @3
    crab
    #
    wcel
    #
    @14
    @2
    @0
    @44
    cF
    vs
    vt
    cS
    cT
    clmod
    clmod
    @36
    @44
    clmhm
    @19
    cS
    wceq
    #
    @15
    cT
    wceq
    #
    wa
    #
    @34
    @43
    vf
    @35
    @3
    @19
    cS
    @15
    cT
    cghm
    oveq12
    @48
    @32
    @43
    vw
    @33
    cvv
    @48
    @19
    csca
    fvexd
    @48
    @17
    @33
    wceq
    #
    wa
    #
    @18
    @5
    @31
    @42
    @50
    @16
    cL
    @17
    cK
    @50
    @16
    cT
    csca
    cfv
    cL
    @50
    @15
    cT
    csca
    @46
    @47
    @49
    simplr
    #
    fveq2d
    islmhm.l
    syl6eqr
    @50
    @17
    cS
    csca
    cfv
    #
    cK
    @50
    @17
    @33
    @52
    @48
    @49
    simpr
    @50
    @19
    cS
    csca
    @46
    @47
    @49
    simpll
    #
    fveq2d
    eqtrd
    islmhm.k
    syl6eqr
    #
    eqeq12d
    @50
    @29
    @41
    vx
    @30
    cB
    @50
    @30
    cK
    cbs
    cfv
    cB
    @50
    @17
    cK
    cbs
    @54
    fveq2d
    islmhm.b
    syl6eqr
    @50
    @27
    @40
    vy
    @28
    cE
    @50
    @28
    cS
    cbs
    cfv
    cE
    @50
    @19
    cS
    cbs
    @53
    fveq2d
    islmhm.e
    syl6eqr
    @50
    @23
    @38
    @26
    @39
    @50
    @21
    @8
    @22
    @50
    @20
    c.x
    @6
    @7
    @50
    @20
    cS
    cvsca
    cfv
    c.x
    @50
    @19
    cS
    cvsca
    @53
    fveq2d
    islmhm.m
    syl6eqr
    oveqd
    fveq2d
    @50
    @25
    c.xp
    @6
    @24
    @50
    @25
    cT
    cvsca
    cfv
    c.xp
    @50
    @15
    cT
    cvsca
    @51
    fveq2d
    islmhm.n
    syl6eqr
    oveqd
    eqeq12d
    raleqbidv
    raleqbidv
    anbi12d
    sbcied
    rabeqbidv
    @37
    @43
    vf
    @3
    cS
    cT
    cghm
    ovex
    rabex
    ovmpt2a
    eleq2d
    @45
    @4
    @5
    @13
    wa
    #
    wa
    @14
    @43
    @55
    vf
    cF
    @3
    @22
    cF
    wceq
    #
    @42
    @13
    @5
    @56
    @40
    @12
    vx
    vy
    cB
    cE
    @56
    @38
    @9
    @39
    @11
    @8
    @22
    cF
    fveq1
    @56
    @24
    @10
    @6
    c.xp
    @7
    @22
    cF
    fveq1
    oveq2d
    eqeq12d
    2ralbidv
    anbi2d
    elrab
    @4
    @5
    @13
    3anass
    bitr4i
    syl6bb
    biadan2
end

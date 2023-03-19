include "wcel.mm"
include "cvv.mm"
include "cdia.mm"
include "cfv.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "ctrl.mm"
include "cltrn.mm"
include "cmpt.mm"
include "wceq.mm"
include "elex.mm"
include "clh.mm"
include "cple.mm"
include "cbs.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "breqd.mm"
include "rabeqbidv.mm"
include "fveq1d.mm"
include "eqidd.mm"
include "breq123d.mm"
include "mpteq12dv.mm"
include "df-disoa.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem diaffval
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cB: class B
  let vf: setvar f
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let vk: setvar k
  let cR: class R
  let cT: class T
  let cW: class W
  let cX: class X
  assume diaval.b: |- B = ( Base ` K )
  assume diaval.l: |- .<_ = ( le ` K )
  assume diaval.h: |- H = ( LHyp ` K )

  disjoint w x
  disjoint w y
  disjoint .<_ w
  disjoint x y
  disjoint .<_ x
  disjoint .<_ y
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint H w
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint K f
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint .<_ k
  disjoint B k
  disjoint H k
  disjoint f k
  disjoint K k
  disjoint R w
  disjoint R x
  disjoint T f
  disjoint T w
  disjoint T x
  disjoint W f
  disjoint W w
  disjoint W x
  disjoint W y
  disjoint X f
  disjoint X x
  disjoint X y
  assert |- ( K e. V -> ( DIsoA ` K ) = ( w e. H |-> ( x e. { y e. B | y .<_ w } |-> { f e. ( ( LTrn ` K ) ` w ) | ( ( ( trL ` K ) ` w ) ` f ) .<_ x } ) ) )

  proof
    cK
    cV
    wcel
    cK
    cvv
    wcel
    cK
    cdia
    cfv
    vw
    cH
    vx
    vy
    cv
    #
    vw
    cv
    #
    c.le
    wbr
    #
    vy
    cB
    crab
    #
    vf
    cv
    #
    @1
    cK
    ctrl
    cfv
    #
    cfv
    #
    cfv
    #
    vx
    cv
    #
    c.le
    wbr
    #
    vf
    @1
    cK
    cltrn
    cfv
    #
    cfv
    #
    crab
    #
    cmpt
    #
    cmpt
    #
    wceq
    cK
    cV
    elex
    vk
    cK
    vw
    vk
    cv
    #
    clh
    cfv
    #
    vx
    @0
    @1
    @15
    cple
    cfv
    #
    wbr
    #
    vy
    @15
    cbs
    cfv
    #
    crab
    #
    @4
    @1
    @15
    ctrl
    cfv
    #
    cfv
    #
    cfv
    #
    @8
    @17
    wbr
    #
    vf
    @1
    @15
    cltrn
    cfv
    #
    cfv
    #
    crab
    #
    cmpt
    #
    cmpt
    @14
    cvv
    cdia
    @15
    cK
    wceq
    #
    vw
    @16
    @28
    cH
    @13
    @29
    @16
    cK
    clh
    cfv
    #
    cH
    @15
    cK
    clh
    fveq2
    diaval.h
    syl6eqr
    @29
    vx
    @20
    @27
    @3
    @12
    @29
    @18
    @2
    vy
    @19
    cB
    @29
    @19
    cK
    cbs
    cfv
    cB
    @15
    cK
    cbs
    fveq2
    diaval.b
    syl6eqr
    @29
    @17
    c.le
    @0
    @1
    @29
    @17
    cK
    cple
    cfv
    c.le
    @15
    cK
    cple
    fveq2
    diaval.l
    syl6eqr
    #
    breqd
    rabeqbidv
    @29
    @24
    @9
    vf
    @26
    @11
    @29
    @1
    @25
    @10
    @15
    cK
    cltrn
    fveq2
    fveq1d
    @29
    @23
    @7
    @8
    @8
    @17
    c.le
    @29
    @4
    @22
    @6
    @29
    @1
    @21
    @5
    @15
    cK
    ctrl
    fveq2
    fveq1d
    fveq1d
    @31
    @29
    @8
    eqidd
    breq123d
    rabeqbidv
    mpteq12dv
    mpteq12dv
    vx
    vy
    vw
    vf
    vk
    df-disoa
    vw
    cH
    @13
    cH
    @30
    cvv
    diaval.h
    cK
    clh
    fvex
    eqeltri
    mptex
    fvmpt
    syl
end

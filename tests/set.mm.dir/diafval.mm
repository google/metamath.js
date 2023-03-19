include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "ctrl.mm"
include "cfv.mm"
include "cltrn.mm"
include "cmpt.mm"
include "cdia.mm"
include "diaffval.mm"
include "fveq1d.mm"
include "syl5eq.mm"
include "wceq.mm"
include "breq2.mm"
include "rabbidv.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "breq1d.mm"
include "rabeqbidv.mm"
include "mpteq12dv.mm"
include "eqid.mm"
include "cbs.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptrabex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem diafval
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let cT: class T
  let vf: setvar f
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vw: setvar w
  let cX: class X
  assume diaval.b: |- B = ( Base ` K )
  assume diaval.l: |- .<_ = ( le ` K )
  assume diaval.h: |- H = ( LHyp ` K )
  assume diaval.t: |- T = ( ( LTrn ` K ) ` W )
  assume diaval.r: |- R = ( ( trL ` K ) ` W )
  assume diaval.i: |- I = ( ( DIsoA ` K ) ` W )

  disjoint x y
  disjoint .<_ x
  disjoint .<_ y
  disjoint B x
  disjoint B y
  disjoint f x
  disjoint f y
  disjoint K f
  disjoint K x
  disjoint K y
  disjoint R x
  disjoint T f
  disjoint T x
  disjoint W f
  disjoint W x
  disjoint W y
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint .<_ k
  disjoint w x
  disjoint w y
  disjoint .<_ w
  disjoint B k
  disjoint B w
  disjoint H k
  disjoint H w
  disjoint f k
  disjoint f w
  disjoint K k
  disjoint K w
  disjoint R w
  disjoint T w
  disjoint W w
  disjoint X f
  disjoint X x
  disjoint X y
  assert |- ( ( K e. V /\ W e. H ) -> I = ( x e. { y e. B | y .<_ W } |-> { f e. T | ( R ` f ) .<_ x } ) )

  proof
    cK
    cV
    wcel
    #
    cW
    cH
    wcel
    cI
    cW
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
    @2
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
    @2
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
    cfv
    #
    vx
    @1
    cW
    c.le
    wbr
    #
    vy
    cB
    crab
    #
    @5
    cR
    cfv
    #
    @9
    c.le
    wbr
    #
    vf
    cT
    crab
    #
    cmpt
    #
    @0
    cI
    cW
    cK
    cdia
    cfv
    #
    cfv
    @16
    diaval.i
    @0
    cW
    @23
    @15
    vx
    vy
    vw
    cB
    vf
    cH
    cK
    c.le
    cV
    diaval.b
    diaval.l
    diaval.h
    diaffval
    fveq1d
    syl5eq
    vw
    cW
    @14
    @22
    cH
    @15
    @2
    cW
    wceq
    #
    vx
    @4
    @13
    @18
    @21
    @24
    @3
    @17
    vy
    cB
    @2
    cW
    @1
    c.le
    breq2
    rabbidv
    @24
    @10
    @20
    vf
    @12
    cT
    @24
    @12
    cW
    @11
    cfv
    cT
    @2
    cW
    @11
    fveq2
    diaval.t
    syl6eqr
    @24
    @8
    @19
    @9
    c.le
    @24
    @5
    @7
    cR
    @24
    @7
    cW
    @6
    cfv
    cR
    @2
    cW
    @6
    fveq2
    diaval.r
    syl6eqr
    fveq1d
    breq1d
    rabeqbidv
    mpteq12dv
    @15
    eqid
    @17
    vx
    vy
    cB
    @21
    cB
    cK
    cbs
    cfv
    cvv
    diaval.b
    cK
    cbs
    fvex
    eqeltri
    mptrabex
    fvmpt
    sylan9eq
end

include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cfv.mm"
include "cv.mm"
include "crab.mm"
include "cmpt.mm"
include "wceq.mm"
include "diafval.mm"
include "adantr.mm"
include "fveq1d.mm"
include "simpr.mm"
include "breq1.mm"
include "elrab.mm"
include "sylibr.mm"
include "breq2.mm"
include "rabbidv.mm"
include "eqid.mm"
include "cltrn.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "fvmpt.mm"
include "syl.mm"
include "eqtrd.mm"

theorem diaval
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
  let cX: class X
  let vk: setvar k
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  assume diaval.b: |- B = ( Base ` K )
  assume diaval.l: |- .<_ = ( le ` K )
  assume diaval.h: |- H = ( LHyp ` K )
  assume diaval.t: |- T = ( ( LTrn ` K ) ` W )
  assume diaval.r: |- R = ( ( trL ` K ) ` W )
  assume diaval.i: |- I = ( ( DIsoA ` K ) ` W )

  disjoint K f
  disjoint T f
  disjoint W f
  disjoint X f
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint .<_ k
  disjoint w x
  disjoint w y
  disjoint .<_ w
  disjoint x y
  disjoint .<_ x
  disjoint .<_ y
  disjoint B k
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint H k
  disjoint H w
  disjoint f k
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint K k
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint R w
  disjoint R x
  disjoint T w
  disjoint T x
  disjoint W w
  disjoint W x
  disjoint W y
  disjoint X x
  disjoint X y
  assert |- ( ( ( K e. V /\ W e. H ) /\ ( X e. B /\ X .<_ W ) ) -> ( I ` X ) = { f e. T | ( R ` f ) .<_ X } )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cB
    wcel
    cX
    cW
    c.le
    wbr
    #
    wa
    #
    wa
    #
    cX
    cI
    cfv
    cX
    vx
    vy
    cv
    #
    cW
    c.le
    wbr
    #
    vy
    cB
    crab
    #
    vf
    cv
    cR
    cfv
    #
    vx
    cv
    #
    c.le
    wbr
    #
    vf
    cT
    crab
    #
    cmpt
    #
    cfv
    #
    @7
    cX
    c.le
    wbr
    #
    vf
    cT
    crab
    #
    @3
    cX
    cI
    @11
    @0
    cI
    @11
    wceq
    @2
    vx
    vy
    cB
    cR
    cT
    vf
    cH
    cI
    cK
    c.le
    cV
    cW
    diaval.b
    diaval.l
    diaval.h
    diaval.t
    diaval.r
    diaval.i
    diafval
    adantr
    fveq1d
    @3
    cX
    @6
    wcel
    #
    @12
    @14
    wceq
    @3
    @2
    @15
    @0
    @2
    simpr
    @5
    @1
    vy
    cX
    cB
    @4
    cX
    cW
    c.le
    breq1
    elrab
    sylibr
    vx
    cX
    @10
    @14
    @6
    @11
    @8
    cX
    wceq
    @9
    @13
    vf
    cT
    @8
    cX
    @7
    c.le
    breq2
    rabbidv
    @11
    eqid
    @13
    vf
    cT
    cT
    cW
    cK
    cltrn
    cfv
    #
    cfv
    cvv
    diaval.t
    cW
    @16
    fvex
    eqeltri
    rabex
    fvmpt
    syl
    eqtrd
end

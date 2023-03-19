include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "cfv.mm"
include "w3a.mm"
include "wrex.mm"
include "cdlemftr3.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "3jca.mm"
include "reximi.mm"
include "syl.mm"

theorem cdlemftr2
  let cB: class B
  let cR: class R
  let cT: class T
  let vf: setvar f
  let cH: class H
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  let vu: setvar u
  let cZ: class Z
  assume cdlemftr.b: |- B = ( Base ` K )
  assume cdlemftr.h: |- H = ( LHyp ` K )
  assume cdlemftr.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemftr.r: |- R = ( ( trL ` K ) ` W )

  disjoint X f
  disjoint Y f
  disjoint H f
  disjoint K f
  disjoint R f
  disjoint T f
  disjoint W f
  disjoint B u
  disjoint f u
  disjoint X u
  disjoint Y u
  disjoint Z u
  disjoint Z f
  disjoint H u
  disjoint K u
  disjoint R u
  disjoint T u
  disjoint W u
  assert |- ( ( K e. HL /\ W e. H ) -> E. f e. T ( f =/= ( _I |` B ) /\ ( R ` f ) =/= X /\ ( R ` f ) =/= Y ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    vf
    cv
    #
    cid
    cB
    cres
    wne
    #
    @0
    cR
    cfv
    #
    cX
    wne
    #
    @2
    cY
    wne
    #
    @4
    w3a
    #
    wa
    #
    vf
    cT
    wrex
    @1
    @3
    @4
    w3a
    #
    vf
    cT
    wrex
    cB
    cR
    cT
    vf
    cH
    cK
    cW
    cX
    cY
    cY
    cdlemftr.b
    cdlemftr.h
    cdlemftr.t
    cdlemftr.r
    cdlemftr3
    @6
    @7
    vf
    cT
    @6
    @1
    @3
    @4
    @1
    @5
    simpl
    @1
    @3
    @4
    @4
    simpr1
    @1
    @3
    @4
    @4
    simpr2
    3jca
    reximi
    syl
end

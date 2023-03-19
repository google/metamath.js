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
include "cdlemftr2.mm"
include "3simpa.mm"
include "reximi.mm"
include "syl.mm"

theorem cdlemftr1
  let cB: class B
  let cR: class R
  let cT: class T
  let vf: setvar f
  let cH: class H
  let cK: class K
  let cW: class W
  let cX: class X
  let vu: setvar u
  let cY: class Y
  let cZ: class Z
  assume cdlemftr.b: |- B = ( Base ` K )
  assume cdlemftr.h: |- H = ( LHyp ` K )
  assume cdlemftr.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemftr.r: |- R = ( ( trL ` K ) ` W )

  disjoint X f
  disjoint H f
  disjoint K f
  disjoint R f
  disjoint T f
  disjoint W f
  disjoint B u
  disjoint f u
  disjoint X u
  disjoint Y u
  disjoint Y f
  disjoint Z u
  disjoint Z f
  disjoint H u
  disjoint K u
  disjoint R u
  disjoint T u
  disjoint W u
  assert |- ( ( K e. HL /\ W e. H ) -> E. f e. T ( f =/= ( _I |` B ) /\ ( R ` f ) =/= X ) )

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
    cX
    wne
    #
    @2
    w3a
    #
    vf
    cT
    wrex
    @1
    @2
    wa
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
    cX
    cdlemftr.b
    cdlemftr.h
    cdlemftr.t
    cdlemftr.r
    cdlemftr2
    @3
    @4
    vf
    cT
    @1
    @2
    @2
    3simpa
    reximi
    syl
end

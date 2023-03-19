include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cfv.mm"
include "cv.mm"
include "crab.mm"
include "diaval.mm"
include "eleq2d.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem diaelval
  let cB: class B
  let cR: class R
  let cT: class T
  let cF: class F
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
  let vf: setvar f
  assume diaval.b: |- B = ( Base ` K )
  assume diaval.l: |- .<_ = ( le ` K )
  assume diaval.h: |- H = ( LHyp ` K )
  assume diaval.t: |- T = ( ( LTrn ` K ) ` W )
  assume diaval.r: |- R = ( ( trL ` K ) ` W )
  assume diaval.i: |- I = ( ( DIsoA ` K ) ` W )


  assert |- ( ( ( K e. V /\ W e. H ) /\ ( X e. B /\ X .<_ W ) ) -> ( F e. ( I ` X ) <-> ( F e. T /\ ( R ` F ) .<_ X ) ) )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    cX
    cB
    wcel
    cX
    cW
    c.le
    wbr
    wa
    wa
    #
    cF
    cX
    cI
    cfv
    #
    wcel
    cF
    vf
    cv
    #
    cR
    cfv
    #
    cX
    c.le
    wbr
    #
    vf
    cT
    crab
    #
    wcel
    cF
    cT
    wcel
    cF
    cR
    cfv
    #
    cX
    c.le
    wbr
    #
    wa
    @0
    @1
    @5
    cF
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
    cX
    diaval.b
    diaval.l
    diaval.h
    diaval.t
    diaval.r
    diaval.i
    diaval
    eleq2d
    @4
    @7
    vf
    cF
    cT
    @2
    cF
    wceq
    @3
    @6
    cX
    c.le
    @2
    cF
    cR
    fveq2
    breq1d
    elrab
    syl6bb
end

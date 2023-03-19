include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cfv.mm"
include "diaelval.mm"
include "simpr.mm"
include "syl6bi.mm"
include "3impia.mm"

theorem diatrl
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
  assume diatrl.b: |- B = ( Base ` K )
  assume diatrl.l: |- .<_ = ( le ` K )
  assume diatrl.h: |- H = ( LHyp ` K )
  assume diatrl.t: |- T = ( ( LTrn ` K ) ` W )
  assume diatrl.r: |- R = ( ( trL ` K ) ` W )
  assume diatrl.i: |- I = ( ( DIsoA ` K ) ` W )


  assert |- ( ( ( K e. V /\ W e. H ) /\ ( X e. B /\ X .<_ W ) /\ F e. ( I ` X ) ) -> ( R ` F ) .<_ X )

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
    wa
    #
    cF
    cX
    cI
    cfv
    wcel
    #
    cF
    cR
    cfv
    cX
    c.le
    wbr
    #
    @0
    @1
    wa
    @2
    cF
    cT
    wcel
    #
    @3
    wa
    @3
    cB
    cR
    cT
    cF
    cH
    cI
    cK
    c.le
    cV
    cW
    cX
    diatrl.b
    diatrl.l
    diatrl.h
    diatrl.t
    diatrl.r
    diatrl.i
    diaelval
    @4
    @3
    simpr
    syl6bi
    3impia
end

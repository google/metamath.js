include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cfv.mm"
include "diass.mm"
include "sseld.mm"
include "3impia.mm"

theorem diael
  let cB: class B
  let cT: class T
  let cF: class F
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let cX: class X
  let vf: setvar f
  assume diass.b: |- B = ( Base ` K )
  assume diass.l: |- .<_ = ( le ` K )
  assume diass.h: |- H = ( LHyp ` K )
  assume diass.t: |- T = ( ( LTrn ` K ) ` W )
  assume diass.i: |- I = ( ( DIsoA ` K ) ` W )


  assert |- ( ( ( K e. V /\ W e. H ) /\ ( X e. B /\ X .<_ W ) /\ F e. ( I ` X ) ) -> F e. T )

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
    #
    wcel
    cF
    cT
    wcel
    @0
    @1
    wa
    @2
    cT
    cF
    cB
    cT
    cH
    cI
    cK
    c.le
    cV
    cW
    cX
    diass.b
    diass.l
    diass.h
    diass.t
    diass.i
    diass
    sseld
    3impia
end

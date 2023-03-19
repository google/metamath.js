include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cfv.mm"
include "cv.mm"
include "ctrl.mm"
include "crab.mm"
include "eqid.mm"
include "diaval.mm"
include "ssrab2.mm"
include "syl6eqss.mm"

theorem diass
  let cB: class B
  let cT: class T
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


  assert |- ( ( ( K e. V /\ W e. H ) /\ ( X e. B /\ X .<_ W ) ) -> ( I ` X ) C_ T )

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
    cX
    cI
    cfv
    vf
    cv
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cfv
    cX
    c.le
    wbr
    #
    vf
    cT
    crab
    cT
    cB
    @0
    cT
    vf
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
    @0
    eqid
    diass.i
    diaval
    @1
    vf
    cT
    ssrab2
    syl6eqss
end

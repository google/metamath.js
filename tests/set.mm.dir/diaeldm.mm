include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "diadm.mm"
include "eleq2d.mm"
include "breq1.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem diaeldm
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  assume diafn.b: |- B = ( Base ` K )
  assume diafn.l: |- .<_ = ( le ` K )
  assume diafn.h: |- H = ( LHyp ` K )
  assume diafn.i: |- I = ( ( DIsoA ` K ) ` W )


  assert |- ( ( K e. V /\ W e. H ) -> ( X e. dom I <-> ( X e. B /\ X .<_ W ) ) )

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
    cI
    cdm
    #
    wcel
    cX
    vx
    cv
    #
    cW
    c.le
    wbr
    #
    vx
    cB
    crab
    #
    wcel
    cX
    cB
    wcel
    cX
    cW
    c.le
    wbr
    #
    wa
    @0
    @1
    @4
    cX
    vx
    cB
    cH
    cI
    cK
    c.le
    cV
    cW
    diafn.b
    diafn.l
    diafn.h
    diafn.i
    diadm
    eleq2d
    @3
    @5
    vx
    cX
    cB
    @2
    cX
    cW
    c.le
    breq1
    elrab
    syl6bb
end

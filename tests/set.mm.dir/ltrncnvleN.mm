include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "claut.mm"
include "cfv.mm"
include "wbr.mm"
include "ccnv.mm"
include "wb.mm"
include "simp1l.mm"
include "eqid.mm"
include "ltrnlaut.mm"
include "3adant3.mm"
include "simp3.mm"
include "lautcnvle.mm"
include "syl21anc.mm"

theorem ltrncnvleN
  let cB: class B
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume ltrnle.b: |- B = ( Base ` K )
  assume ltrnle.l: |- .<_ = ( le ` K )
  assume ltrnle.h: |- H = ( LHyp ` K )
  assume ltrnle.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. V /\ W e. H ) /\ F e. T /\ ( X e. B /\ Y e. B ) ) -> ( X .<_ Y <-> ( `' F ` X ) .<_ ( `' F ` Y ) ) )

  proof
    cK
    cV
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cF
    cT
    wcel
    #
    cX
    cB
    wcel
    cY
    cB
    wcel
    wa
    #
    w3a
    @0
    cF
    cK
    claut
    cfv
    #
    wcel
    #
    @4
    cX
    cY
    c.le
    wbr
    cX
    cF
    ccnv
    #
    cfv
    cY
    @7
    cfv
    c.le
    wbr
    wb
    @0
    @1
    @3
    @4
    simp1l
    @2
    @3
    @6
    @4
    cT
    cF
    cH
    @5
    cK
    cV
    cW
    ltrnle.h
    @5
    eqid
    #
    ltrnle.t
    ltrnlaut
    3adant3
    @2
    @3
    @4
    simp3
    cB
    cF
    @5
    cK
    c.le
    cV
    cX
    cY
    ltrnle.b
    ltrnle.l
    @8
    lautcnvle
    syl21anc
end

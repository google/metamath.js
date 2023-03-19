include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "claut.mm"
include "cfv.mm"
include "wbr.mm"
include "wb.mm"
include "simp1l.mm"
include "eqid.mm"
include "ltrnlaut.mm"
include "3adant3.mm"
include "simp3l.mm"
include "simp3r.mm"
include "lautcvr.mm"
include "syl13anc.mm"

theorem ltrncvr
  let cB: class B
  let cC: class C
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume ltrncvr.b: |- B = ( Base ` K )
  assume ltrncvr.c: |- C = ( <o ` K )
  assume ltrncvr.h: |- H = ( LHyp ` K )
  assume ltrncvr.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. V /\ W e. H ) /\ F e. T /\ ( X e. B /\ Y e. B ) ) -> ( X C Y <-> ( F ` X ) C ( F ` Y ) ) )

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
    #
    cY
    cB
    wcel
    #
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
    @5
    cX
    cY
    cC
    wbr
    cX
    cF
    cfv
    cY
    cF
    cfv
    cC
    wbr
    wb
    @0
    @1
    @3
    @6
    simp1l
    @2
    @3
    @8
    @6
    cT
    cF
    cH
    @7
    cK
    cV
    cW
    ltrncvr.h
    @7
    eqid
    #
    ltrncvr.t
    ltrnlaut
    3adant3
    @2
    @3
    @4
    @5
    simp3l
    @2
    @3
    @4
    @5
    simp3r
    cV
    cB
    cC
    cF
    @7
    cK
    cX
    cY
    ltrncvr.b
    ltrncvr.c
    @9
    lautcvr
    syl13anc
end

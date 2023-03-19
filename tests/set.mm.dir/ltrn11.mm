include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "claut.mm"
include "cfv.mm"
include "wceq.mm"
include "wb.mm"
include "simp1l.mm"
include "eqid.mm"
include "ltrnlaut.mm"
include "3adant3.mm"
include "simp3l.mm"
include "simp3r.mm"
include "laut11.mm"
include "syl22anc.mm"

theorem ltrn11
  let cB: class B
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume ltrn1o.b: |- B = ( Base ` K )
  assume ltrn1o.h: |- H = ( LHyp ` K )
  assume ltrn1o.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. V /\ W e. H ) /\ F e. T /\ ( X e. B /\ Y e. B ) ) -> ( ( F ` X ) = ( F ` Y ) <-> X = Y ) )

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
    cF
    cfv
    cY
    cF
    cfv
    wceq
    cX
    cY
    wceq
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
    ltrn1o.h
    @7
    eqid
    #
    ltrn1o.t
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
    cB
    cF
    @7
    cK
    cV
    cX
    cY
    ltrn1o.b
    @9
    laut11
    syl22anc
end

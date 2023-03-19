include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "claut.mm"
include "cfv.mm"
include "simp1l.mm"
include "eqid.mm"
include "ltrnlaut.mm"
include "3adant3.mm"
include "simp3.mm"
include "lautcl.mm"
include "syl21anc.mm"

theorem ltrncl
  let cB: class B
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  assume ltrn1o.b: |- B = ( Base ` K )
  assume ltrn1o.h: |- H = ( LHyp ` K )
  assume ltrn1o.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. V /\ W e. H ) /\ F e. T /\ X e. B ) -> ( F ` X ) e. B )

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
    cF
    cfv
    cB
    wcel
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
    ltrn1o.h
    @5
    eqid
    #
    ltrn1o.t
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
    cV
    cX
    ltrn1o.b
    @7
    lautcl
    syl21anc
end

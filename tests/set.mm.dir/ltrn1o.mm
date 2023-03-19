include "wcel.mm"
include "wa.mm"
include "claut.mm"
include "cfv.mm"
include "wf1o.mm"
include "simpll.mm"
include "eqid.mm"
include "ltrnlaut.mm"
include "laut1o.mm"
include "syl2anc.mm"

theorem ltrn1o
  let cB: class B
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  assume ltrn1o.b: |- B = ( Base ` K )
  assume ltrn1o.h: |- H = ( LHyp ` K )
  assume ltrn1o.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. V /\ W e. H ) /\ F e. T ) -> F : B -1-1-onto-> B )

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
    cF
    cT
    wcel
    #
    wa
    @0
    cF
    cK
    claut
    cfv
    #
    wcel
    cB
    cB
    cF
    wf1o
    @0
    @1
    @2
    simpll
    cT
    cF
    cH
    @3
    cK
    cV
    cW
    ltrn1o.h
    @3
    eqid
    #
    ltrn1o.t
    ltrnlaut
    cV
    cB
    cF
    @3
    cK
    ltrn1o.b
    @4
    laut1o
    syl2anc
end

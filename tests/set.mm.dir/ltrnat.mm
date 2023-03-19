include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cfv.mm"
include "simp3.mm"
include "cbs.mm"
include "wb.mm"
include "eqid.mm"
include "atbase.mm"
include "ltrnatb.mm"
include "syl3an3.mm"
include "mpbid.mm"

theorem ltrnat
  let cA: class A
  let cP: class P
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume ltrnel.l: |- .<_ = ( le ` K )
  assume ltrnel.a: |- A = ( Atoms ` K )
  assume ltrnel.h: |- H = ( LHyp ` K )
  assume ltrnel.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ P e. A ) -> ( F ` P ) e. A )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cF
    cT
    wcel
    #
    cP
    cA
    wcel
    #
    w3a
    @2
    cP
    cF
    cfv
    cA
    wcel
    #
    @0
    @1
    @2
    simp3
    @2
    @0
    @1
    cP
    cK
    cbs
    cfv
    #
    wcel
    @2
    @3
    wb
    cA
    @4
    cP
    cK
    @4
    eqid
    #
    ltrnel.a
    atbase
    cA
    @4
    cP
    cT
    cF
    cH
    cK
    cW
    @5
    ltrnel.a
    ltrnel.h
    ltrnel.t
    ltrnatb
    syl3an3
    mpbid
end

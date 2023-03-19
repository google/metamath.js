include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "simp1.mm"
include "simp2l.mm"
include "ltrnel.mm"
include "3adant2l.mm"
include "syl3anc.mm"

theorem ltrncoelN
  let cA: class A
  let cP: class P
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume ltrnel.l: |- .<_ = ( le ` K )
  assume ltrnel.a: |- A = ( Atoms ` K )
  assume ltrnel.h: |- H = ( LHyp ` K )
  assume ltrnel.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ G e. T ) /\ ( P e. A /\ -. P .<_ W ) ) -> ( ( F ` ( G ` P ) ) e. A /\ -. ( F ` ( G ` P ) ) .<_ W ) )

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
    cG
    cT
    wcel
    #
    wa
    #
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    @0
    @1
    cP
    cG
    cfv
    #
    cA
    wcel
    @5
    cW
    c.le
    wbr
    wn
    wa
    #
    @5
    cF
    cfv
    #
    cA
    wcel
    @7
    cW
    c.le
    wbr
    wn
    wa
    @0
    @3
    @4
    simp1
    @0
    @1
    @2
    @4
    simp2l
    @0
    @2
    @4
    @6
    @1
    cA
    cP
    cT
    cG
    cH
    cK
    c.le
    cW
    ltrnel.l
    ltrnel.a
    ltrnel.h
    ltrnel.t
    ltrnel
    3adant2l
    cA
    @5
    cT
    cF
    cH
    cK
    c.le
    cW
    ltrnel.l
    ltrnel.a
    ltrnel.h
    ltrnel.t
    ltrnel
    syl3anc
end

include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "wne.mm"
include "ltrn2ateq.mm"
include "necon3bid.mm"
include "biimp3a.mm"

theorem ltrnatneq
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume ltrn2eq.l: |- .<_ = ( le ` K )
  assume ltrn2eq.a: |- A = ( Atoms ` K )
  assume ltrn2eq.h: |- H = ( LHyp ` K )
  assume ltrn2eq.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F ` P ) =/= P ) -> ( F ` Q ) =/= Q )

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
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    w3a
    #
    cP
    cF
    cfv
    #
    cP
    wne
    cQ
    cF
    cfv
    #
    cQ
    wne
    @0
    @1
    wa
    @2
    cP
    @3
    cQ
    cA
    cP
    cQ
    cT
    cF
    cH
    cK
    c.le
    cW
    ltrn2eq.l
    ltrn2eq.a
    ltrn2eq.h
    ltrn2eq.t
    ltrn2ateq
    necon3bid
    biimp3a
end

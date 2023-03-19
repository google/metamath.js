include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "wne.mm"
include "wrex.mm"
include "lhpexle.mm"
include "adantr.mm"
include "co.mm"
include "w3a.mm"
include "simpll.mm"
include "simpr.mm"
include "simplr.mm"
include "cdlemf1.mm"
include "syl3anc.mm"
include "3simpa.mm"
include "reximi.mm"
include "syl.mm"
include "rexlimddv.mm"

theorem cdlemg5
  let cA: class A
  let cP: class P
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vq: setvar q
  let vr: setvar r
  assume cdlemg5.l: |- .<_ = ( le ` K )
  assume cdlemg5.j: |- .\/ = ( join ` K )
  assume cdlemg5.a: |- A = ( Atoms ` K )
  assume cdlemg5.h: |- H = ( LHyp ` K )

  disjoint A q
  disjoint H q
  disjoint K q
  disjoint .<_ q
  disjoint P q
  disjoint W q
  disjoint q r
  disjoint A r
  disjoint H r
  disjoint K r
  disjoint .<_ r
  disjoint P r
  disjoint W r
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) ) -> E. q e. A ( P =/= q /\ -. q .<_ W ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
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
    wa
    #
    vr
    cv
    #
    cW
    c.le
    wbr
    #
    cP
    vq
    cv
    #
    wne
    #
    @5
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    vq
    cA
    wrex
    #
    vr
    cA
    @0
    @4
    vr
    cA
    wrex
    @1
    cA
    cH
    cK
    c.le
    cW
    vr
    cdlemg5.l
    cdlemg5.a
    cdlemg5.h
    lhpexle
    adantr
    @2
    @3
    cA
    wcel
    @4
    wa
    #
    wa
    #
    @6
    @7
    @3
    cP
    @5
    c.or
    co
    c.le
    wbr
    #
    w3a
    #
    vq
    cA
    wrex
    #
    @9
    @11
    @0
    @10
    @1
    @14
    @0
    @1
    @10
    simpll
    @2
    @10
    simpr
    @0
    @1
    @10
    simplr
    cA
    cP
    @3
    cH
    c.or
    cK
    c.le
    cW
    vq
    cdlemg5.l
    cdlemg5.j
    cdlemg5.a
    cdlemg5.h
    cdlemf1
    syl3anc
    @13
    @8
    vq
    cA
    @6
    @7
    @12
    3simpa
    reximi
    syl
    rexlimddv
end

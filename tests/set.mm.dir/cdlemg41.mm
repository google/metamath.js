include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "ccom.mm"
include "cdlemg40.mm"
include "wceq.mm"
include "simp1.mm"
include "simp3.mm"
include "simp2ll.mm"
include "ltrncoval.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "simp2rl.mm"
include "3eqtr4d.mm"

theorem cdlemg41
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdlemg35.l: |- .<_ = ( le ` K )
  assume cdlemg35.j: |- .\/ = ( join ` K )
  assume cdlemg35.m: |- ./\ = ( meet ` K )
  assume cdlemg35.a: |- A = ( Atoms ` K )
  assume cdlemg35.h: |- H = ( LHyp ` K )
  assume cdlemg35.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T ) ) -> ( ( P .\/ ( ( F o. G ) ` P ) ) ./\ W ) = ( ( Q .\/ ( ( F o. G ) ` Q ) ) ./\ W ) )

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
    #
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cQ
    cA
    wcel
    #
    cQ
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    wa
    #
    cF
    cT
    wcel
    cG
    cT
    wcel
    wa
    #
    w3a
    #
    cP
    cP
    cG
    cfv
    cF
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    cQ
    cQ
    cG
    cfv
    cF
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    cP
    cP
    cF
    cG
    ccom
    #
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    cQ
    cQ
    @14
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    cA
    cP
    cQ
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg35.l
    cdlemg35.j
    cdlemg35.m
    cdlemg35.a
    cdlemg35.h
    cdlemg35.t
    cdlemg40
    @9
    @16
    @11
    cW
    c.an
    @9
    @15
    @10
    cP
    c.or
    @9
    @0
    @8
    @1
    @15
    @10
    wceq
    @0
    @7
    @8
    simp1
    #
    @0
    @7
    @8
    simp3
    #
    @1
    @2
    @6
    @0
    @8
    simp2ll
    cA
    cP
    cT
    cF
    cG
    cH
    cK
    c.le
    cW
    cdlemg35.l
    cdlemg35.a
    cdlemg35.h
    cdlemg35.t
    ltrncoval
    syl3anc
    oveq2d
    oveq1d
    @9
    @18
    @13
    cW
    c.an
    @9
    @17
    @12
    cQ
    c.or
    @9
    @0
    @8
    @4
    @17
    @12
    wceq
    @19
    @20
    @4
    @5
    @3
    @0
    @8
    simp2rl
    cA
    cQ
    cT
    cF
    cG
    cH
    cK
    c.le
    cW
    cdlemg35.l
    cdlemg35.a
    cdlemg35.h
    cdlemg35.t
    ltrncoval
    syl3anc
    oveq2d
    oveq1d
    3eqtr4d
end

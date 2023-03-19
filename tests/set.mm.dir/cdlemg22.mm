include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "simpl11.mm"
include "simpl12.mm"
include "simpl13.mm"
include "simpl21.mm"
include "simpl22.mm"
include "simpr.mm"
include "cdlemg14f.mm"
include "syl123anc.mm"
include "simpl1.mm"
include "jca.mm"
include "simpl23.mm"
include "simpl31.mm"
include "simpl32.mm"
include "simpl33.mm"
include "cdlemg21.mm"
include "syl133anc.mm"
include "pm2.61dane.mm"

theorem cdlemg22
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let vr: setvar r
  let cS: class S
  assume cdlemg12.l: |- .<_ = ( le ` K )
  assume cdlemg12.j: |- .\/ = ( join ` K )
  assume cdlemg12.m: |- ./\ = ( meet ` K )
  assume cdlemg12.a: |- A = ( Atoms ` K )
  assume cdlemg12.h: |- H = ( LHyp ` K )
  assume cdlemg12.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg12b.r: |- R = ( ( trL ` K ) ` W )

  disjoint A r
  disjoint G r
  disjoint .\/ r
  disjoint .<_ r
  disjoint P r
  disjoint Q r
  disjoint W r
  disjoint F r
  disjoint S r
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T /\ P =/= Q ) /\ ( ( R ` F ) .<_ ( P .\/ Q ) /\ ( ( F ` ( G ` P ) ) .\/ ( F ` ( G ` Q ) ) ) =/= ( P .\/ Q ) /\ -. E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ W ) = ( ( Q .\/ ( F ` ( G ` Q ) ) ) ./\ W ) )

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
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    cF
    cT
    wcel
    #
    cG
    cT
    wcel
    #
    cP
    cQ
    wne
    #
    w3a
    #
    cF
    cR
    cfv
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    cP
    cG
    cfv
    cF
    cfv
    #
    cQ
    cG
    cfv
    cF
    cfv
    #
    c.or
    co
    @8
    wne
    #
    vr
    cv
    #
    cW
    c.le
    wbr
    wn
    cP
    @13
    c.or
    co
    cQ
    @13
    c.or
    co
    wceq
    wa
    vr
    cA
    wrex
    wn
    #
    w3a
    #
    w3a
    #
    cP
    @10
    c.or
    co
    cW
    c.an
    co
    cQ
    @11
    c.or
    co
    cW
    c.an
    co
    wceq
    #
    cP
    cF
    cfv
    #
    cP
    @16
    @18
    cP
    wceq
    #
    wa
    @0
    @1
    @2
    @4
    @5
    @19
    @17
    @0
    @1
    @2
    @7
    @15
    @19
    simpl11
    @0
    @1
    @2
    @7
    @15
    @19
    simpl12
    @0
    @1
    @2
    @7
    @15
    @19
    simpl13
    @4
    @5
    @6
    @3
    @15
    @19
    simpl21
    @4
    @5
    @6
    @3
    @15
    @19
    simpl22
    @16
    @19
    simpr
    cA
    cP
    cQ
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg14f
    syl123anc
    @16
    @18
    cP
    wne
    #
    wa
    #
    @3
    @4
    @5
    wa
    @6
    @20
    @9
    @12
    @14
    @17
    @3
    @7
    @15
    @20
    simpl1
    @21
    @4
    @5
    @4
    @5
    @6
    @3
    @15
    @20
    simpl21
    @4
    @5
    @6
    @3
    @15
    @20
    simpl22
    jca
    @4
    @5
    @6
    @3
    @15
    @20
    simpl23
    @16
    @20
    simpr
    @9
    @12
    @14
    @3
    @7
    @20
    simpl31
    @9
    @12
    @14
    @3
    @7
    @20
    simpl32
    @9
    @12
    @14
    @3
    @7
    @20
    simpl33
    cA
    cP
    cQ
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    vr
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg21
    syl133anc
    pm2.61dane
end

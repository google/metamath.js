include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cv.mm"
include "cp0.mm"
include "cfv.mm"
include "wceq.mm"
include "wne.mm"
include "co.mm"
include "wrex.mm"
include "simp1.mm"
include "simp21.mm"
include "simp22r.mm"
include "simp22l.mm"
include "jca.mm"
include "simp23r.mm"
include "simp23l.mm"
include "simp3.mm"
include "cdlemg33c.mm"
include "syl131anc.mm"
include "3ancoma.mm"
include "anbi2i.mm"
include "rexbii.mm"
include "sylib.mm"

theorem cdlemg33d
  let vz: setvar z
  let vv: setvar v
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
  let cN: class N
  let cO: class O
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
  assume cdlemg31.n: |- N = ( ( P .\/ v ) ./\ ( Q .\/ ( R ` F ) ) )
  assume cdlemg33.o: |- O = ( ( P .\/ v ) ./\ ( Q .\/ ( R ` G ) ) )

  disjoint A r
  disjoint G r
  disjoint .\/ r
  disjoint .<_ r
  disjoint P r
  disjoint Q r
  disjoint W r
  disjoint F r
  disjoint A z
  disjoint F z
  disjoint r z
  disjoint H r
  disjoint H z
  disjoint .\/ z
  disjoint K r
  disjoint K z
  disjoint .<_ z
  disjoint N r
  disjoint N z
  disjoint P z
  disjoint Q z
  disjoint R z
  disjoint T z
  disjoint W z
  disjoint v z
  disjoint r v
  disjoint G z
  disjoint O z
  disjoint O r
  disjoint S r
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( v e. A /\ v .<_ W ) /\ ( N = ( 0. ` K ) /\ O e. A ) /\ ( F e. T /\ G e. T ) ) /\ ( P =/= Q /\ v =/= ( R ` G ) /\ E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> E. z e. A ( -. z .<_ W /\ ( z =/= N /\ z =/= O /\ z .<_ ( P .\/ v ) ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
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
    vv
    cv
    #
    cA
    wcel
    @1
    cW
    c.le
    wbr
    wa
    #
    cN
    cK
    cp0
    cfv
    wceq
    #
    cO
    cA
    wcel
    #
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
    w3a
    #
    cP
    cQ
    wne
    @1
    cG
    cR
    cfv
    wne
    vr
    cv
    #
    cW
    c.le
    wbr
    wn
    cP
    @10
    c.or
    co
    cQ
    @10
    c.or
    co
    wceq
    wa
    vr
    cA
    wrex
    w3a
    #
    w3a
    #
    vz
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @13
    cO
    wne
    #
    @13
    cN
    wne
    #
    @13
    cP
    @1
    c.or
    co
    c.le
    wbr
    #
    w3a
    #
    wa
    #
    vz
    cA
    wrex
    #
    @14
    @16
    @15
    @17
    w3a
    #
    wa
    #
    vz
    cA
    wrex
    @12
    @0
    @2
    @4
    @3
    wa
    @7
    @6
    wa
    @11
    @20
    @0
    @9
    @11
    simp1
    @0
    @2
    @5
    @8
    @11
    simp21
    @12
    @4
    @3
    @3
    @4
    @2
    @8
    @0
    @11
    simp22r
    @3
    @4
    @2
    @8
    @0
    @11
    simp22l
    jca
    @12
    @7
    @6
    @6
    @7
    @2
    @5
    @0
    @11
    simp23r
    @6
    @7
    @2
    @5
    @0
    @11
    simp23l
    jca
    @0
    @9
    @11
    simp3
    vz
    vv
    cA
    cP
    cQ
    cR
    cT
    cG
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cO
    cN
    cW
    vr
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg33.o
    cdlemg31.n
    cdlemg33c
    syl131anc
    @19
    @22
    vz
    cA
    @18
    @21
    @14
    @15
    @16
    @17
    3ancoma
    anbi2i
    rexbii
    sylib
end

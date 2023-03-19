include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cv.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "cp0.mm"
include "wo.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp21.mm"
include "simp22l.mm"
include "simp31.mm"
include "cdlemg31b0a.mm"
include "syl132anc.mm"
include "simp22r.mm"
include "simp32.mm"
include "simpl1.mm"
include "simpl21.mm"
include "simpr.mm"
include "simpl22.mm"
include "simpl23.mm"
include "simpl31.mm"
include "simpl33.mm"
include "cdlemg33b.mm"
include "syl133anc.mm"
include "ex.mm"
include "simpl32.mm"
include "cdlemg33d.mm"
include "cdlemg33c.mm"
include "cdlemg33e.mm"
include "ccased.mm"
include "mp2and.mm"

theorem cdlemg33
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( v e. A /\ v .<_ W ) /\ ( F e. T /\ G e. T ) /\ P =/= Q ) /\ ( v =/= ( R ` F ) /\ v =/= ( R ` G ) /\ E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> E. z e. A ( -. z .<_ W /\ ( z =/= N /\ z =/= O /\ z .<_ ( P .\/ v ) ) ) )

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
    vv
    cv
    #
    cA
    wcel
    @4
    cW
    c.le
    wbr
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
    cQ
    wne
    #
    w3a
    #
    @4
    cF
    cR
    cfv
    wne
    #
    @4
    cG
    cR
    cfv
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
    #
    w3a
    #
    w3a
    #
    cN
    cA
    wcel
    #
    cN
    cK
    cp0
    cfv
    #
    wceq
    #
    wo
    #
    cO
    cA
    wcel
    #
    cO
    @18
    wceq
    #
    wo
    #
    vz
    cv
    #
    cW
    c.le
    wbr
    wn
    @24
    cN
    wne
    @24
    cO
    wne
    @24
    cP
    @4
    c.or
    co
    c.le
    wbr
    w3a
    wa
    vz
    cA
    wrex
    #
    @16
    @0
    @1
    @2
    @5
    @6
    @11
    @20
    @0
    @1
    @2
    @10
    @15
    simp11
    #
    @0
    @1
    @2
    @10
    @15
    simp12
    #
    @0
    @1
    @2
    @10
    @15
    simp13
    #
    @3
    @5
    @8
    @9
    @15
    simp21
    #
    @6
    @7
    @5
    @9
    @3
    @15
    simp22l
    @3
    @10
    @11
    @12
    @14
    simp31
    vv
    cA
    cP
    cQ
    cR
    cT
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cW
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg31.n
    cdlemg31b0a
    syl132anc
    @16
    @0
    @1
    @2
    @5
    @7
    @12
    @23
    @26
    @27
    @28
    @29
    @6
    @7
    @5
    @9
    @3
    @15
    simp22r
    @3
    @10
    @11
    @12
    @14
    simp32
    vv
    cA
    cP
    cQ
    cR
    cT
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cO
    cW
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg33.o
    cdlemg31b0a
    syl132anc
    @16
    @17
    @21
    @19
    @22
    @25
    @16
    @17
    @21
    wa
    #
    @25
    @16
    @30
    wa
    @3
    @5
    @30
    @8
    @9
    @11
    @14
    @25
    @3
    @10
    @15
    @30
    simpl1
    @5
    @8
    @9
    @3
    @15
    @30
    simpl21
    @16
    @30
    simpr
    @5
    @8
    @9
    @3
    @15
    @30
    simpl22
    @5
    @8
    @9
    @3
    @15
    @30
    simpl23
    @11
    @12
    @14
    @3
    @10
    @30
    simpl31
    @11
    @12
    @14
    @3
    @10
    @30
    simpl33
    vz
    vv
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
    cN
    cO
    cW
    vr
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg31.n
    cdlemg33.o
    cdlemg33b
    syl133anc
    ex
    @16
    @19
    @21
    wa
    #
    @25
    @16
    @31
    wa
    @3
    @5
    @31
    @8
    @9
    @12
    @14
    @25
    @3
    @10
    @15
    @31
    simpl1
    @5
    @8
    @9
    @3
    @15
    @31
    simpl21
    @16
    @31
    simpr
    @5
    @8
    @9
    @3
    @15
    @31
    simpl22
    @5
    @8
    @9
    @3
    @15
    @31
    simpl23
    @11
    @12
    @14
    @3
    @10
    @31
    simpl32
    @11
    @12
    @14
    @3
    @10
    @31
    simpl33
    vz
    vv
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
    cN
    cO
    cW
    vr
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg31.n
    cdlemg33.o
    cdlemg33d
    syl133anc
    ex
    @16
    @17
    @22
    wa
    #
    @25
    @16
    @32
    wa
    @3
    @5
    @32
    @8
    @9
    @11
    @14
    @25
    @3
    @10
    @15
    @32
    simpl1
    @5
    @8
    @9
    @3
    @15
    @32
    simpl21
    @16
    @32
    simpr
    @5
    @8
    @9
    @3
    @15
    @32
    simpl22
    @5
    @8
    @9
    @3
    @15
    @32
    simpl23
    @11
    @12
    @14
    @3
    @10
    @32
    simpl31
    @11
    @12
    @14
    @3
    @10
    @32
    simpl33
    vz
    vv
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
    cN
    cO
    cW
    vr
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg31.n
    cdlemg33.o
    cdlemg33c
    syl133anc
    ex
    @16
    @19
    @22
    wa
    #
    @25
    @16
    @33
    wa
    @3
    @5
    @33
    @8
    @9
    @11
    @14
    @25
    @3
    @10
    @15
    @33
    simpl1
    @5
    @8
    @9
    @3
    @15
    @33
    simpl21
    @16
    @33
    simpr
    @5
    @8
    @9
    @3
    @15
    @33
    simpl22
    @5
    @8
    @9
    @3
    @15
    @33
    simpl23
    @11
    @12
    @14
    @3
    @10
    @33
    simpl31
    @11
    @12
    @14
    @3
    @10
    @33
    simpl33
    vz
    vv
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
    cN
    cO
    cW
    vr
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg31.n
    cdlemg33.o
    cdlemg33e
    syl133anc
    ex
    ccased
    mp2and
end

include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cv.mm"
include "wne.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "simp11.mm"
include "simp13.mm"
include "simp22.mm"
include "simp23l.mm"
include "simp23r.mm"
include "simp1.mm"
include "simp22l.mm"
include "simp21.mm"
include "simp311.mm"
include "jca.mm"
include "simp32l.mm"
include "simp313.mm"
include "simp33l.mm"
include "cdlemg27b.mm"
include "syl133anc.mm"
include "simp312.mm"
include "simp32r.mm"
include "simp33r.mm"
include "cdlemg26zz.mm"

theorem cdlemg28b
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

  disjoint A z
  disjoint F z
  disjoint H z
  disjoint .\/ z
  disjoint K z
  disjoint .<_ z
  disjoint N z
  disjoint P z
  disjoint Q z
  disjoint R z
  disjoint T z
  disjoint W z
  disjoint v z
  disjoint G z
  disjoint O z
  disjoint A r
  disjoint G r
  disjoint .\/ r
  disjoint .<_ r
  disjoint P r
  disjoint Q r
  disjoint W r
  disjoint F r
  disjoint S r
  disjoint r z
  disjoint H r
  disjoint K r
  disjoint N r
  disjoint r v
  disjoint O r
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( v e. A /\ v .<_ W ) /\ ( z e. A /\ -. z .<_ W ) /\ ( F e. T /\ G e. T ) ) /\ ( ( z =/= N /\ z =/= O /\ z .<_ ( P .\/ v ) ) /\ ( v =/= ( R ` F ) /\ v =/= ( R ` G ) ) /\ ( ( F ` P ) =/= P /\ ( G ` P ) =/= P ) ) ) -> ( ( Q .\/ ( F ` ( G ` Q ) ) ) ./\ W ) = ( ( z .\/ ( F ` ( G ` z ) ) ) ./\ W ) )

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
    vz
    cv
    #
    cA
    wcel
    #
    @6
    cW
    c.le
    wbr
    wn
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
    @6
    cN
    wne
    #
    @6
    cO
    wne
    #
    @6
    cP
    @4
    c.or
    co
    c.le
    wbr
    #
    w3a
    #
    @4
    cF
    cR
    cfv
    #
    wne
    #
    @4
    cG
    cR
    cfv
    #
    wne
    #
    wa
    #
    cP
    cF
    cfv
    cP
    wne
    #
    cP
    cG
    cfv
    cP
    wne
    #
    wa
    #
    w3a
    #
    w3a
    #
    @0
    @2
    @9
    @10
    @11
    @18
    cQ
    @6
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    @20
    @28
    c.le
    wbr
    wn
    #
    cQ
    cQ
    cG
    cfv
    cF
    cfv
    c.or
    co
    cW
    c.an
    co
    @6
    @6
    cG
    cfv
    cF
    cfv
    c.or
    co
    cW
    c.an
    co
    wceq
    @0
    @1
    @2
    @13
    @26
    simp11
    @0
    @1
    @2
    @13
    @26
    simp13
    @3
    @5
    @9
    @12
    @26
    simp22
    @10
    @11
    @5
    @9
    @3
    @26
    simp23l
    #
    @10
    @11
    @5
    @9
    @3
    @26
    simp23r
    #
    @27
    @3
    @7
    @5
    @10
    @14
    wa
    @19
    @16
    @23
    @29
    @3
    @13
    @26
    simp1
    #
    @7
    @8
    @5
    @12
    @3
    @26
    simp22l
    #
    @3
    @5
    @9
    @12
    @26
    simp21
    #
    @27
    @10
    @14
    @31
    @14
    @15
    @16
    @22
    @25
    @3
    @13
    simp311
    jca
    @19
    @21
    @17
    @25
    @3
    @13
    simp32l
    @14
    @15
    @16
    @22
    @25
    @3
    @13
    simp313
    #
    @23
    @24
    @17
    @22
    @3
    @13
    simp33l
    vz
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
    cdlemg27b
    syl133anc
    @27
    @3
    @7
    @5
    @11
    @15
    wa
    @21
    @16
    @24
    @30
    @33
    @34
    @35
    @27
    @11
    @15
    @32
    @14
    @15
    @16
    @22
    @25
    @3
    @13
    simp312
    jca
    @19
    @21
    @17
    @25
    @3
    @13
    simp32r
    @36
    @23
    @24
    @17
    @22
    @3
    @13
    simp33r
    vz
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
    cdlemg27b
    syl133anc
    vz
    cA
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
    cdlemg26zz
    syl133anc
end

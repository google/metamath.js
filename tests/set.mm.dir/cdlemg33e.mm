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
include "simp23l.mm"
include "simp3.mm"
include "cdlemg33c0.mm"
include "syl121anc.mm"
include "cal.mm"
include "simp11l.mm"
include "hlatl.mm"
include "syl.mm"
include "eqid.mm"
include "atn0.mm"
include "sylan.mm"
include "simp22l.mm"
include "adantr.mm"
include "neeqtrrd.mm"
include "simp22r.mm"
include "jca.mm"
include "biantrurd.mm"
include "df-3an.mm"
include "syl6bbr.mm"
include "anbi2d.mm"
include "rexbidva.mm"
include "mpbid.mm"

theorem cdlemg33e
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( v e. A /\ v .<_ W ) /\ ( N = ( 0. ` K ) /\ O = ( 0. ` K ) ) /\ ( F e. T /\ G e. T ) ) /\ ( P =/= Q /\ v =/= ( R ` F ) /\ E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> E. z e. A ( -. z .<_ W /\ ( z =/= N /\ z =/= O /\ z .<_ ( P .\/ v ) ) ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
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
    @5
    cW
    c.le
    wbr
    wa
    #
    cN
    cK
    cp0
    cfv
    #
    wceq
    #
    cO
    @7
    wceq
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
    @5
    cF
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
    @15
    c.or
    co
    cQ
    @15
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
    @18
    cP
    @5
    c.or
    co
    c.le
    wbr
    #
    wa
    #
    vz
    cA
    wrex
    #
    @19
    @18
    cN
    wne
    #
    @18
    cO
    wne
    #
    @20
    w3a
    #
    wa
    #
    vz
    cA
    wrex
    @17
    @4
    @6
    @11
    @16
    @22
    @4
    @14
    @16
    simp1
    @4
    @6
    @10
    @13
    @16
    simp21
    @11
    @12
    @6
    @10
    @4
    @16
    simp23l
    @4
    @14
    @16
    simp3
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
    vr
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg31.n
    cdlemg33c0
    syl121anc
    @17
    @21
    @26
    vz
    cA
    @17
    @18
    cA
    wcel
    #
    wa
    #
    @20
    @25
    @19
    @28
    @20
    @23
    @24
    wa
    #
    @20
    wa
    @25
    @28
    @29
    @20
    @28
    @23
    @24
    @28
    @18
    @7
    cN
    @17
    cK
    cal
    wcel
    #
    @27
    @18
    @7
    wne
    @17
    @0
    @30
    @0
    @1
    @2
    @3
    @14
    @16
    simp11l
    cK
    hlatl
    syl
    cA
    @18
    cK
    @7
    @7
    eqid
    cdlemg12.a
    atn0
    sylan
    #
    @17
    @8
    @27
    @8
    @9
    @6
    @13
    @4
    @16
    simp22l
    adantr
    neeqtrrd
    @28
    @18
    @7
    cO
    @31
    @17
    @9
    @27
    @8
    @9
    @6
    @13
    @4
    @16
    simp22r
    adantr
    neeqtrrd
    jca
    biantrurd
    @23
    @24
    @20
    df-3an
    syl6bbr
    anbi2d
    rexbidva
    mpbid
end

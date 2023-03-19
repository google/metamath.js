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
include "df-3an.mm"
include "anidm.mm"
include "neeq2.mm"
include "anbi2d.mm"
include "syl5rbbr.mm"
include "anbi1d.mm"
include "syl5bb.mm"
include "rexbidv.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl31.mm"
include "simpr.mm"
include "jca.mm"
include "simpl32.mm"
include "simpl33.mm"
include "cdlemg33a.mm"
include "syl113anc.mm"
include "simp21.mm"
include "simp22l.mm"
include "simp23l.mm"
include "3jca.mm"
include "cdlemg33b0.mm"
include "syld3an2.mm"
include "pm2.61ne.mm"

theorem cdlemg33b
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( v e. A /\ v .<_ W ) /\ ( N e. A /\ O e. A ) /\ ( F e. T /\ G e. T ) ) /\ ( P =/= Q /\ v =/= ( R ` F ) /\ E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> E. z e. A ( -. z .<_ W /\ ( z =/= N /\ z =/= O /\ z .<_ ( P .\/ v ) ) ) )

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
    cA
    wcel
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
    #
    @1
    cF
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
    @12
    c.or
    co
    cQ
    @12
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
    vz
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @16
    cN
    wne
    #
    @16
    cO
    wne
    #
    @16
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
    @17
    @18
    @20
    wa
    #
    wa
    #
    vz
    cA
    wrex
    #
    cN
    cO
    cN
    cO
    wceq
    #
    @22
    @25
    vz
    cA
    @27
    @21
    @24
    @17
    @21
    @18
    @19
    wa
    #
    @20
    wa
    @27
    @24
    @18
    @19
    @20
    df-3an
    @27
    @28
    @18
    @20
    @18
    @18
    @18
    wa
    @27
    @28
    @18
    anidm
    @27
    @18
    @19
    @18
    cN
    cO
    @16
    neeq2
    anbi2d
    syl5rbbr
    anbi1d
    syl5bb
    anbi2d
    rexbidv
    @15
    cN
    cO
    wne
    #
    wa
    #
    @0
    @9
    @10
    @29
    wa
    @11
    @13
    @23
    @0
    @9
    @14
    @29
    simpl1
    @0
    @9
    @14
    @29
    simpl2
    @30
    @10
    @29
    @10
    @11
    @13
    @0
    @9
    @29
    simpl31
    @15
    @29
    simpr
    jca
    @10
    @11
    @13
    @0
    @9
    @29
    simpl32
    @10
    @11
    @13
    @0
    @9
    @29
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
    cdlemg33a
    syl113anc
    @0
    @2
    @3
    @6
    w3a
    @9
    @14
    @26
    @15
    @2
    @3
    @6
    @0
    @2
    @5
    @8
    @14
    simp21
    @3
    @4
    @2
    @8
    @0
    @14
    simp22l
    @6
    @7
    @2
    @5
    @0
    @14
    simp23l
    3jca
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
    cdlemg33b0
    syld3an2
    pm2.61ne
end

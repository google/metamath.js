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
include "simpl11.mm"
include "simpl12.mm"
include "simpl13.mm"
include "simp23l.mm"
include "adantr.mm"
include "simp23r.mm"
include "simpr.mm"
include "cdlemg14f.mm"
include "syl123anc.mm"
include "cdlemg14g.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simp31l.mm"
include "simp31r.mm"
include "simpl32.mm"
include "3jca.mm"
include "simpl33.mm"
include "cdlemg28.mm"
include "syl113anc.mm"
include "pm2.61da2ne.mm"

theorem cdlemg29
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( v e. A /\ v .<_ W ) /\ ( z e. A /\ -. z .<_ W ) /\ ( F e. T /\ G e. T ) ) /\ ( ( z =/= N /\ z =/= O ) /\ z .<_ ( P .\/ v ) /\ ( v =/= ( R ` F ) /\ v =/= ( R ` G ) ) ) ) -> ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ W ) = ( ( Q .\/ ( F ` ( G ` Q ) ) ) ./\ W ) )

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
    @6
    cW
    c.le
    wbr
    wn
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
    wa
    #
    @6
    cP
    @4
    c.or
    co
    c.le
    wbr
    #
    @4
    cF
    cR
    cfv
    wne
    @4
    cG
    cR
    cfv
    wne
    wa
    #
    w3a
    #
    w3a
    #
    cP
    cP
    cG
    cfv
    #
    cF
    cfv
    c.or
    co
    cW
    c.an
    co
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
    wceq
    #
    cP
    cF
    cfv
    #
    cP
    @18
    cP
    @17
    @20
    cP
    wceq
    #
    wa
    @0
    @1
    @2
    @8
    @9
    @21
    @19
    @0
    @1
    @2
    @10
    @16
    @21
    simpl11
    @0
    @1
    @2
    @10
    @16
    @21
    simpl12
    @0
    @1
    @2
    @10
    @16
    @21
    simpl13
    @17
    @8
    @21
    @8
    @9
    @5
    @7
    @3
    @16
    simp23l
    #
    adantr
    @17
    @9
    @21
    @8
    @9
    @5
    @7
    @3
    @16
    simp23r
    #
    adantr
    @17
    @21
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
    @17
    @18
    cP
    wceq
    #
    wa
    @0
    @1
    @2
    @8
    @9
    @24
    @19
    @0
    @1
    @2
    @10
    @16
    @24
    simpl11
    @0
    @1
    @2
    @10
    @16
    @24
    simpl12
    @0
    @1
    @2
    @10
    @16
    @24
    simpl13
    @17
    @8
    @24
    @22
    adantr
    @17
    @9
    @24
    @23
    adantr
    @17
    @24
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
    cdlemg14g
    syl123anc
    @17
    @20
    cP
    wne
    @18
    cP
    wne
    wa
    #
    wa
    #
    @3
    @10
    @11
    @12
    @14
    w3a
    @15
    @25
    @19
    @3
    @10
    @16
    @25
    simpl1
    @3
    @10
    @16
    @25
    simpl2
    @26
    @11
    @12
    @14
    @17
    @11
    @25
    @11
    @12
    @14
    @15
    @3
    @10
    simp31l
    adantr
    @17
    @12
    @25
    @11
    @12
    @14
    @15
    @3
    @10
    simp31r
    adantr
    @13
    @14
    @15
    @3
    @10
    @25
    simpl32
    3jca
    @13
    @14
    @15
    @3
    @10
    @25
    simpl33
    @17
    @25
    simpr
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
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg31.n
    cdlemg33.o
    cdlemg28
    syl113anc
    pm2.61da2ne
end

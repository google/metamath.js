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
include "cdlemg33.mm"
include "simp11.mm"
include "simp121.mm"
include "simp2.mm"
include "simp3l.mm"
include "jca.mm"
include "simp122.mm"
include "simp3r1.mm"
include "simp3r2.mm"
include "simp3r3.mm"
include "simp131.mm"
include "simp132.mm"
include "cdlemg29.mm"
include "syl133anc.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem cdlemg34
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
  let vz: setvar z
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
  disjoint H r
  disjoint K r
  disjoint N r
  disjoint r v
  disjoint O r
  disjoint S r
  disjoint A z
  disjoint F z
  disjoint r z
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
  disjoint ./\ z
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( v e. A /\ v .<_ W ) /\ ( F e. T /\ G e. T ) /\ P =/= Q ) /\ ( v =/= ( R ` F ) /\ v =/= ( R ` G ) /\ E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ W ) = ( ( Q .\/ ( F ` ( G ` Q ) ) ) ./\ W ) )

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
    cF
    cT
    wcel
    cG
    cT
    wcel
    wa
    #
    cP
    cQ
    wne
    #
    w3a
    #
    @1
    cF
    cR
    cfv
    wne
    #
    @1
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
    @8
    c.or
    co
    cQ
    @8
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
    @12
    cN
    wne
    #
    @12
    cO
    wne
    #
    @12
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
    cP
    cP
    cG
    cfv
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
    cdlemg33
    @11
    @18
    @19
    vz
    cA
    @11
    @12
    cA
    wcel
    #
    @18
    w3a
    #
    @0
    @2
    @20
    @13
    wa
    @3
    @14
    @15
    wa
    @16
    @6
    @7
    wa
    @19
    @0
    @5
    @10
    @20
    @18
    simp11
    @2
    @3
    @4
    @0
    @10
    @20
    @18
    simp121
    @21
    @20
    @13
    @11
    @20
    @18
    simp2
    @11
    @20
    @13
    @17
    simp3l
    jca
    @2
    @3
    @4
    @0
    @10
    @20
    @18
    simp122
    @21
    @14
    @15
    @14
    @15
    @16
    @13
    @11
    @20
    simp3r1
    @14
    @15
    @16
    @13
    @11
    @20
    simp3r2
    jca
    @14
    @15
    @16
    @13
    @11
    @20
    simp3r3
    @21
    @6
    @7
    @6
    @7
    @9
    @0
    @5
    @20
    @18
    simp131
    @6
    @7
    @9
    @0
    @5
    @20
    @18
    simp132
    jca
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
    cdlemg29
    syl133anc
    rexlimdv3a
    mpd
end

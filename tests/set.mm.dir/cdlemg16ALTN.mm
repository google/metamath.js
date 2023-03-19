include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "simpl11.mm"
include "simpl12.mm"
include "jca.mm"
include "simpl21.mm"
include "simpl22.mm"
include "simpl13.mm"
include "simpr.mm"
include "simpl31.mm"
include "cdlemg15a.mm"
include "syl312anc.mm"
include "simp13l.mm"
include "adantr.mm"
include "simp13r.mm"
include "simpl23.mm"
include "simpl32.mm"
include "simpl33.mm"
include "cdlemg12.mm"
include "syl333anc.mm"
include "pm2.61dane.mm"

theorem cdlemg16ALTN
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
  assume cdlemg12.l: |- .<_ = ( le ` K )
  assume cdlemg12.j: |- .\/ = ( join ` K )
  assume cdlemg12.m: |- ./\ = ( meet ` K )
  assume cdlemg12.a: |- A = ( Atoms ` K )
  assume cdlemg12.h: |- H = ( LHyp ` K )
  assume cdlemg12.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg12b.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H /\ ( F e. T /\ G e. T ) ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ P =/= Q ) /\ ( ( ( F ` ( G ` P ) ) .\/ ( F ` ( G ` Q ) ) ) =/= ( P .\/ Q ) /\ -. ( R ` F ) .<_ ( P .\/ Q ) /\ -. ( R ` G ) .<_ ( P .\/ Q ) ) ) -> ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ W ) = ( ( Q .\/ ( F ` ( G ` Q ) ) ) ./\ W ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
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
    cP
    cQ
    wne
    #
    w3a
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
    cP
    cQ
    c.or
    co
    #
    wne
    #
    cF
    cR
    cfv
    #
    @12
    c.le
    wbr
    wn
    #
    cG
    cR
    cfv
    #
    @12
    c.le
    wbr
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
    @14
    @16
    @19
    @14
    @16
    wceq
    #
    wa
    #
    @0
    @1
    wa
    #
    @6
    @7
    @4
    @21
    @13
    @20
    @22
    @0
    @1
    @0
    @1
    @4
    @9
    @18
    @21
    simpl11
    @0
    @1
    @4
    @9
    @18
    @21
    simpl12
    jca
    @6
    @7
    @8
    @5
    @18
    @21
    simpl21
    @6
    @7
    @8
    @5
    @18
    @21
    simpl22
    @0
    @1
    @4
    @9
    @18
    @21
    simpl13
    @19
    @21
    simpr
    @13
    @15
    @17
    @5
    @9
    @21
    simpl31
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
    cdlemg15a
    syl312anc
    @19
    @14
    @16
    wne
    #
    wa
    #
    @23
    @6
    @7
    @2
    @3
    @8
    @15
    @17
    wa
    @24
    @13
    @20
    @25
    @0
    @1
    @0
    @1
    @4
    @9
    @18
    @24
    simpl11
    @0
    @1
    @4
    @9
    @18
    @24
    simpl12
    jca
    @6
    @7
    @8
    @5
    @18
    @24
    simpl21
    @6
    @7
    @8
    @5
    @18
    @24
    simpl22
    @19
    @2
    @24
    @2
    @3
    @0
    @1
    @9
    @18
    simp13l
    adantr
    @19
    @3
    @24
    @2
    @3
    @0
    @1
    @9
    @18
    simp13r
    adantr
    @6
    @7
    @8
    @5
    @18
    @24
    simpl23
    @25
    @15
    @17
    @13
    @15
    @17
    @5
    @9
    @24
    simpl32
    @13
    @15
    @17
    @5
    @9
    @24
    simpl33
    jca
    @19
    @24
    simpr
    @13
    @15
    @17
    @5
    @9
    @24
    simpl31
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
    cdlemg12
    syl333anc
    pm2.61dane
end

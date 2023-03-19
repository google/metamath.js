include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl21.mm"
include "simpl22.mm"
include "simpr.mm"
include "cdlemg15.mm"
include "syl121anc.mm"
include "simpl2.mm"
include "simpl31.mm"
include "simpl32.mm"
include "jca.mm"
include "simpl33.mm"
include "cdlemg12.mm"
include "syl113anc.mm"
include "pm2.61dane.mm"

theorem cdlemg16
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T /\ P =/= Q ) /\ ( -. ( R ` F ) .<_ ( P .\/ Q ) /\ -. ( R ` G ) .<_ ( P .\/ Q ) /\ ( ( F ` ( G ` P ) ) .\/ ( F ` ( G ` Q ) ) ) =/= ( P .\/ Q ) ) ) -> ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ W ) = ( ( Q .\/ ( F ` ( G ` Q ) ) ) ./\ W ) )

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
    #
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    cG
    cR
    cfv
    #
    @6
    c.le
    wbr
    wn
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
    @6
    wne
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
    @5
    @8
    @14
    @5
    @8
    wceq
    #
    wa
    @0
    @1
    @2
    @16
    @15
    @0
    @4
    @13
    @16
    simpl1
    @1
    @2
    @3
    @0
    @13
    @16
    simpl21
    @1
    @2
    @3
    @0
    @13
    @16
    simpl22
    @14
    @16
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
    cdlemg15
    syl121anc
    @14
    @5
    @8
    wne
    #
    wa
    #
    @0
    @4
    @7
    @9
    wa
    @17
    @12
    @15
    @0
    @4
    @13
    @17
    simpl1
    @0
    @4
    @13
    @17
    simpl2
    @18
    @7
    @9
    @7
    @9
    @12
    @0
    @4
    @17
    simpl31
    @7
    @9
    @12
    @0
    @4
    @17
    simpl32
    jca
    @14
    @17
    simpr
    @7
    @9
    @12
    @0
    @4
    @17
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
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg12
    syl113anc
    pm2.61dane
end

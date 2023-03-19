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
include "simpl11.mm"
include "simpl12.mm"
include "simpl13.mm"
include "simpl21.mm"
include "simpl22.mm"
include "simpr.mm"
include "cdlemg8.mm"
include "syl132anc.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3l.mm"
include "simpl3r.mm"
include "cdlemg16.mm"
include "syl113anc.mm"
include "pm2.61dane.mm"

theorem cdlemg16z
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T /\ P =/= Q ) /\ ( -. ( R ` F ) .<_ ( P .\/ Q ) /\ -. ( R ` G ) .<_ ( P .\/ Q ) ) ) -> ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ W ) = ( ( Q .\/ ( F ` ( G ` Q ) ) ) ./\ W ) )

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
    wn
    #
    cG
    cR
    cfv
    @8
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    cP
    cP
    cG
    cfv
    cF
    cfv
    #
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
    #
    c.or
    co
    cW
    c.an
    co
    wceq
    #
    @13
    @14
    c.or
    co
    #
    @8
    @12
    @16
    @8
    wceq
    #
    wa
    @0
    @1
    @2
    @4
    @5
    @17
    @15
    @0
    @1
    @2
    @7
    @11
    @17
    simpl11
    @0
    @1
    @2
    @7
    @11
    @17
    simpl12
    @0
    @1
    @2
    @7
    @11
    @17
    simpl13
    @4
    @5
    @6
    @3
    @11
    @17
    simpl21
    @4
    @5
    @6
    @3
    @11
    @17
    simpl22
    @12
    @17
    simpr
    cA
    cP
    cQ
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
    cdlemg8
    syl132anc
    @12
    @16
    @8
    wne
    #
    wa
    @3
    @7
    @9
    @10
    @18
    @15
    @3
    @7
    @11
    @18
    simpl1
    @3
    @7
    @11
    @18
    simpl2
    @9
    @10
    @3
    @7
    @18
    simpl3l
    @9
    @10
    @3
    @7
    @18
    simpl3r
    @12
    @18
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
    cdlemg16
    syl113anc
    pm2.61dane
end

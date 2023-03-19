include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "co.mm"
include "wne.mm"
include "simpl11.mm"
include "simpl12.mm"
include "simpl13.mm"
include "simpl2l.mm"
include "simpl2r.mm"
include "simpr.mm"
include "cdlemg14f.mm"
include "syl123anc.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3l.mm"
include "simpl3r.mm"
include "cdlemg13.mm"
include "syl113anc.mm"
include "pm2.61dane.mm"

theorem cdlemg15a
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T ) /\ ( ( R ` F ) = ( R ` G ) /\ ( ( F ` ( G ` P ) ) .\/ ( F ` ( G ` Q ) ) ) =/= ( P .\/ Q ) ) ) -> ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ W ) = ( ( Q .\/ ( F ` ( G ` Q ) ) ) ./\ W ) )

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
    wa
    #
    cF
    cR
    cfv
    cG
    cR
    cfv
    wceq
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
    wne
    #
    wa
    #
    w3a
    #
    cP
    @8
    c.or
    co
    cW
    c.an
    co
    cQ
    @9
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
    @12
    @14
    cP
    wceq
    #
    wa
    @0
    @1
    @2
    @4
    @5
    @15
    @13
    @0
    @1
    @2
    @6
    @11
    @15
    simpl11
    @0
    @1
    @2
    @6
    @11
    @15
    simpl12
    @0
    @1
    @2
    @6
    @11
    @15
    simpl13
    @4
    @5
    @3
    @11
    @15
    simpl2l
    @4
    @5
    @3
    @11
    @15
    simpl2r
    @12
    @15
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
    @12
    @14
    cP
    wne
    #
    wa
    @3
    @6
    @16
    @7
    @10
    @13
    @3
    @6
    @11
    @16
    simpl1
    @3
    @6
    @11
    @16
    simpl2
    @12
    @16
    simpr
    @7
    @10
    @3
    @6
    @16
    simpl3l
    @7
    @10
    @3
    @6
    @16
    simpl3r
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
    cdlemg13
    syl113anc
    pm2.61dane
end

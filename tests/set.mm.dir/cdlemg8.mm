include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl21.mm"
include "simpl22.mm"
include "simpl23.mm"
include "simpl3l.mm"
include "simpr.mm"
include "cdlemg8a.mm"
include "syl123anc.mm"
include "wne.mm"
include "simpl2.mm"
include "simpl3r.mm"
include "cdlemg8d.mm"
include "syl113anc.mm"
include "pm2.61dane.mm"

theorem cdlemg8
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdlemg8.l: |- .<_ = ( le ` K )
  assume cdlemg8.j: |- .\/ = ( join ` K )
  assume cdlemg8.m: |- ./\ = ( meet ` K )
  assume cdlemg8.a: |- A = ( Atoms ` K )
  assume cdlemg8.h: |- H = ( LHyp ` K )
  assume cdlemg8.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ F e. T ) /\ ( G e. T /\ ( ( F ` ( G ` P ) ) .\/ ( F ` ( G ` Q ) ) ) = ( P .\/ Q ) ) ) -> ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ W ) = ( ( Q .\/ ( F ` ( G ` Q ) ) ) ./\ W ) )

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
    cF
    cT
    wcel
    #
    w3a
    #
    cG
    cT
    wcel
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
    wceq
    #
    wa
    #
    w3a
    #
    cP
    @6
    c.or
    co
    cW
    c.an
    co
    cQ
    @7
    c.or
    co
    cW
    c.an
    co
    wceq
    #
    @6
    cP
    @10
    @6
    cP
    wceq
    #
    wa
    @0
    @1
    @2
    @3
    @5
    @12
    @11
    @0
    @4
    @9
    @12
    simpl1
    @1
    @2
    @3
    @0
    @9
    @12
    simpl21
    @1
    @2
    @3
    @0
    @9
    @12
    simpl22
    @1
    @2
    @3
    @0
    @9
    @12
    simpl23
    @5
    @8
    @0
    @4
    @12
    simpl3l
    @10
    @12
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
    cdlemg8.l
    cdlemg8.j
    cdlemg8.m
    cdlemg8.a
    cdlemg8.h
    cdlemg8.t
    cdlemg8a
    syl123anc
    @10
    @6
    cP
    wne
    #
    wa
    @0
    @4
    @5
    @8
    @13
    @11
    @0
    @4
    @9
    @13
    simpl1
    @0
    @4
    @9
    @13
    simpl2
    @5
    @8
    @0
    @4
    @13
    simpl3l
    @5
    @8
    @0
    @4
    @13
    simpl3r
    @10
    @13
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
    cdlemg8.l
    cdlemg8.j
    cdlemg8.m
    cdlemg8.a
    cdlemg8.h
    cdlemg8.t
    cdlemg8d
    syl113anc
    pm2.61dane
end

include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpr.mm"
include "simpl3l.mm"
include "simpl3r.mm"
include "cdlemg22.mm"
include "syl113anc.mm"
include "cdlemg20.mm"
include "simprl.mm"
include "simprr.mm"
include "cdlemg16z.mm"
include "syl112anc.mm"
include "pm2.61ddan.mm"

theorem cdlemg24
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
  let vr: setvar r
  let cS: class S
  assume cdlemg12.l: |- .<_ = ( le ` K )
  assume cdlemg12.j: |- .\/ = ( join ` K )
  assume cdlemg12.m: |- ./\ = ( meet ` K )
  assume cdlemg12.a: |- A = ( Atoms ` K )
  assume cdlemg12.h: |- H = ( LHyp ` K )
  assume cdlemg12.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg12b.r: |- R = ( ( trL ` K ) ` W )

  disjoint A r
  disjoint G r
  disjoint .\/ r
  disjoint .<_ r
  disjoint P r
  disjoint Q r
  disjoint W r
  disjoint F r
  disjoint S r
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T /\ P =/= Q ) /\ ( ( ( F ` ( G ` P ) ) .\/ ( F ` ( G ` Q ) ) ) =/= ( P .\/ Q ) /\ -. E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ W ) = ( ( Q .\/ ( F ` ( G ` Q ) ) ) ./\ W ) )

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
    cG
    cT
    wcel
    cP
    cQ
    wne
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
    vr
    cv
    #
    cW
    c.le
    wbr
    wn
    cP
    @6
    c.or
    co
    cQ
    @6
    c.or
    co
    wceq
    wa
    vr
    cA
    wrex
    wn
    #
    wa
    #
    w3a
    #
    cF
    cR
    cfv
    @4
    c.le
    wbr
    #
    cG
    cR
    cfv
    @4
    c.le
    wbr
    #
    cP
    @2
    c.or
    co
    cW
    c.an
    co
    cQ
    @3
    c.or
    co
    cW
    c.an
    co
    wceq
    #
    @9
    @10
    wa
    @0
    @1
    @10
    @5
    @7
    @12
    @0
    @1
    @8
    @10
    simpl1
    @0
    @1
    @8
    @10
    simpl2
    @9
    @10
    simpr
    @5
    @7
    @0
    @1
    @10
    simpl3l
    @5
    @7
    @0
    @1
    @10
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
    vr
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg22
    syl113anc
    @9
    @11
    wa
    @0
    @1
    @11
    @5
    @7
    @12
    @0
    @1
    @8
    @11
    simpl1
    @0
    @1
    @8
    @11
    simpl2
    @9
    @11
    simpr
    @5
    @7
    @0
    @1
    @11
    simpl3l
    @5
    @7
    @0
    @1
    @11
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
    vr
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg20
    syl113anc
    @9
    @10
    wn
    #
    @11
    wn
    #
    wa
    #
    wa
    @0
    @1
    @13
    @14
    @12
    @0
    @1
    @8
    @15
    simpl1
    @0
    @1
    @8
    @15
    simpl2
    @9
    @13
    @14
    simprl
    @9
    @13
    @14
    simprr
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
    cdlemg16z
    syl112anc
    pm2.61ddan
end

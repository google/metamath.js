include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3l.mm"
include "simpl3r.mm"
include "simpr.mm"
include "cdlemg36.mm"
include "syl113anc.mm"
include "simpl11.mm"
include "simpl12.mm"
include "simpl13.mm"
include "simpl21.mm"
include "simpl22.mm"
include "simpl23.mm"
include "cdlemg37.mm"
include "syl133anc.mm"
include "pm2.61dan.mm"

theorem cdlemg38
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
  let vv: setvar v
  let vr: setvar r
  assume cdlemg35.l: |- .<_ = ( le ` K )
  assume cdlemg35.j: |- .\/ = ( join ` K )
  assume cdlemg35.m: |- ./\ = ( meet ` K )
  assume cdlemg35.a: |- A = ( Atoms ` K )
  assume cdlemg35.h: |- H = ( LHyp ` K )
  assume cdlemg35.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg35.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T /\ P =/= Q ) /\ ( ( ( F ` P ) =/= P /\ ( G ` P ) =/= P ) /\ ( R ` F ) =/= ( R ` G ) ) ) -> ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ W ) = ( ( Q .\/ ( F ` ( G ` Q ) ) ) ./\ W ) )

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
    cP
    cF
    cfv
    cP
    wne
    cP
    cG
    cfv
    #
    cP
    wne
    wa
    #
    cF
    cR
    cfv
    cG
    cR
    cfv
    wne
    #
    wa
    #
    w3a
    #
    vr
    cv
    #
    cW
    c.le
    wbr
    wn
    cP
    @13
    c.or
    co
    cQ
    @13
    c.or
    co
    wceq
    wa
    vr
    cA
    wrex
    #
    cP
    @8
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
    @12
    @14
    wa
    @3
    @7
    @9
    @10
    @14
    @15
    @3
    @7
    @11
    @14
    simpl1
    @3
    @7
    @11
    @14
    simpl2
    @9
    @10
    @3
    @7
    @14
    simpl3l
    @9
    @10
    @3
    @7
    @14
    simpl3r
    @12
    @14
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
    vr
    cdlemg35.l
    cdlemg35.j
    cdlemg35.m
    cdlemg35.a
    cdlemg35.h
    cdlemg35.t
    cdlemg35.r
    cdlemg36
    syl113anc
    @12
    @14
    wn
    #
    wa
    @0
    @1
    @2
    @4
    @5
    @6
    @16
    @15
    @0
    @1
    @2
    @7
    @11
    @16
    simpl11
    @0
    @1
    @2
    @7
    @11
    @16
    simpl12
    @0
    @1
    @2
    @7
    @11
    @16
    simpl13
    @4
    @5
    @6
    @3
    @11
    @16
    simpl21
    @4
    @5
    @6
    @3
    @11
    @16
    simpl22
    @4
    @5
    @6
    @3
    @11
    @16
    simpl23
    @12
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
    vr
    cdlemg35.l
    cdlemg35.j
    cdlemg35.m
    cdlemg35.a
    cdlemg35.h
    cdlemg35.t
    cdlemg35.r
    cdlemg37
    syl133anc
    pm2.61dan
end

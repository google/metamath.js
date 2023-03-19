include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "ctrl.mm"
include "cjn.mm"
include "co.mm"
include "simpl1.mm"
include "simpl2l.mm"
include "simpl2r.mm"
include "simpl31.mm"
include "simpl32.mm"
include "simpr.mm"
include "simpl33.mm"
include "eqid.mm"
include "cdlemg6e.mm"
include "syl133anc.mm"
include "cdlemg4.mm"
include "pm2.61dan.mm"

theorem cdlemg6
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume cdlemg6.l: |- .<_ = ( le ` K )
  assume cdlemg6.a: |- A = ( Atoms ` K )
  assume cdlemg6.h: |- H = ( LHyp ` K )
  assume cdlemg6.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T /\ ( F ` ( G ` P ) ) = P ) ) -> ( F ` ( G ` Q ) ) = Q )

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
    cP
    cG
    cfv
    cF
    cfv
    cP
    wceq
    #
    w3a
    #
    w3a
    #
    cQ
    cP
    cG
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cfv
    #
    cK
    cjn
    cfv
    #
    co
    c.le
    wbr
    #
    cQ
    cG
    cfv
    cF
    cfv
    cQ
    wceq
    #
    @8
    @12
    wa
    @0
    @1
    @2
    @4
    @5
    @12
    @6
    @13
    @0
    @3
    @7
    @12
    simpl1
    @1
    @2
    @0
    @7
    @12
    simpl2l
    @1
    @2
    @0
    @7
    @12
    simpl2r
    @4
    @5
    @6
    @0
    @3
    @12
    simpl31
    @4
    @5
    @6
    @0
    @3
    @12
    simpl32
    @8
    @12
    simpr
    @4
    @5
    @6
    @0
    @3
    @12
    simpl33
    cA
    cP
    cQ
    @9
    cT
    cF
    cG
    cH
    @11
    cK
    c.le
    @10
    cW
    cdlemg6.l
    cdlemg6.a
    cdlemg6.h
    cdlemg6.t
    @9
    eqid
    #
    @11
    eqid
    #
    @10
    eqid
    #
    cdlemg6e
    syl133anc
    @8
    @12
    wn
    #
    wa
    @0
    @1
    @2
    @4
    @5
    @17
    @6
    @13
    @0
    @3
    @7
    @17
    simpl1
    @1
    @2
    @0
    @7
    @17
    simpl2l
    @1
    @2
    @0
    @7
    @17
    simpl2r
    @4
    @5
    @6
    @0
    @3
    @17
    simpl31
    @4
    @5
    @6
    @0
    @3
    @17
    simpl32
    @8
    @17
    simpr
    @4
    @5
    @6
    @0
    @3
    @17
    simpl33
    cA
    cP
    cQ
    @9
    cT
    cF
    cG
    cH
    @11
    cK
    c.le
    @10
    cW
    cdlemg6.l
    cdlemg6.a
    cdlemg6.h
    cdlemg6.t
    @14
    @15
    @16
    cdlemg4
    syl133anc
    pm2.61dan
end

include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "w3a.mm"
include "cbs.mm"
include "cfv.mm"
include "cp1.mm"
include "ccvr.mm"
include "cv.mm"
include "co.mm"
include "wrex.mm"
include "simp1l.mm"
include "simp2ll.mm"
include "simp2rl.mm"
include "simp1r.mm"
include "eqid.mm"
include "lhpbase.mm"
include "syl.mm"
include "simp3.mm"
include "lhp1cvr.mm"
include "3ad2ant1.mm"
include "simp2lr.mm"
include "simp2rr.mm"
include "cdlemb.mm"
include "syl323anc.mm"

theorem cdlemb2
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vr: setvar r
  assume cdlemb2.l: |- .<_ = ( le ` K )
  assume cdlemb2.j: |- .\/ = ( join ` K )
  assume cdlemb2.a: |- A = ( Atoms ` K )
  assume cdlemb2.h: |- H = ( LHyp ` K )

  disjoint A r
  disjoint .\/ r
  disjoint K r
  disjoint .<_ r
  disjoint P r
  disjoint Q r
  disjoint W r
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ P =/= Q ) -> E. r e. A ( -. r .<_ W /\ -. r .<_ ( P .\/ Q ) ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cQ
    cA
    wcel
    #
    cQ
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    wa
    #
    cP
    cQ
    wne
    #
    w3a
    #
    @0
    @3
    @6
    cW
    cK
    cbs
    cfv
    #
    wcel
    #
    @10
    cW
    cK
    cp1
    cfv
    #
    cK
    ccvr
    cfv
    #
    wbr
    #
    @4
    @7
    vr
    cv
    #
    cW
    c.le
    wbr
    wn
    @17
    cP
    cQ
    c.or
    co
    c.le
    wbr
    wn
    wa
    vr
    cA
    wrex
    @0
    @1
    @9
    @10
    simp1l
    @3
    @4
    @8
    @2
    @10
    simp2ll
    @6
    @7
    @5
    @2
    @10
    simp2rl
    @11
    @1
    @13
    @0
    @1
    @9
    @10
    simp1r
    @12
    cH
    cK
    cW
    @12
    eqid
    #
    cdlemb2.h
    lhpbase
    syl
    @2
    @9
    @10
    simp3
    @2
    @9
    @16
    @10
    chlt
    @15
    @14
    cH
    cK
    cW
    @14
    eqid
    #
    @15
    eqid
    #
    cdlemb2.h
    lhp1cvr
    3ad2ant1
    @3
    @4
    @8
    @2
    @10
    simp2lr
    @6
    @7
    @5
    @2
    @10
    simp2rr
    cA
    @12
    @15
    cP
    cQ
    @14
    c.or
    cK
    c.le
    cW
    vr
    @18
    cdlemb2.l
    cdlemb2.j
    @19
    @20
    cdlemb2.a
    cdlemb
    syl323anc
end

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
include "co.mm"
include "simp1l.mm"
include "simp2l.mm"
include "simp3l.mm"
include "simp1r.mm"
include "eqid.mm"
include "lhpbase.mm"
include "syl.mm"
include "simp3r.mm"
include "lhp1cvr.mm"
include "3ad2ant1.mm"
include "simp2r.mm"
include "1cvrat.mm"
include "syl133anc.mm"

theorem lhpat
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume lhpat.l: |- .<_ = ( le ` K )
  assume lhpat.j: |- .\/ = ( join ` K )
  assume lhpat.m: |- ./\ = ( meet ` K )
  assume lhpat.a: |- A = ( Atoms ` K )
  assume lhpat.h: |- H = ( LHyp ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ P =/= Q ) ) -> ( ( P .\/ Q ) ./\ W ) e. A )

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
    cP
    cQ
    wne
    #
    wa
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
    @7
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
    cP
    cQ
    c.or
    co
    cW
    c.an
    co
    cA
    wcel
    @0
    @1
    @5
    @8
    simp1l
    @2
    @3
    @4
    @8
    simp2l
    @2
    @5
    @6
    @7
    simp3l
    @9
    @1
    @11
    @0
    @1
    @5
    @8
    simp1r
    @10
    cH
    cK
    cW
    @10
    eqid
    #
    lhpat.h
    lhpbase
    syl
    @2
    @5
    @6
    @7
    simp3r
    @2
    @5
    @14
    @8
    chlt
    @13
    @12
    cH
    cK
    cW
    @12
    eqid
    #
    @13
    eqid
    #
    lhpat.h
    lhp1cvr
    3ad2ant1
    @2
    @3
    @4
    @8
    simp2r
    cA
    @10
    @13
    cP
    cQ
    @12
    c.or
    cK
    c.le
    c.an
    cW
    @15
    lhpat.l
    lhpat.j
    lhpat.m
    @16
    @17
    lhpat.a
    1cvrat
    syl133anc
end

include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "simp11l.mm"
include "simp1r1.mm"
include "3ad2ant1.mm"
include "simp1r2.mm"
include "simp2.mm"
include "simp3l.mm"
include "jca.mm"
include "simp1r3.mm"
include "simp3r.mm"
include "simp12.mm"
include "simp13.mm"
include "cmee.mm"
include "cfv.mm"
include "eqid.mm"
include "4atexlemex6.mm"
include "syl323anc.mm"
include "rexlimdv3a.mm"
include "3exp.mm"
include "3impd.mm"
include "3impia.mm"

theorem 4atexlem7
  let vz: setvar z
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vr: setvar r
  assume 4that.l: |- .<_ = ( le ` K )
  assume 4that.j: |- .\/ = ( join ` K )
  assume 4that.a: |- A = ( Atoms ` K )
  assume 4that.h: |- H = ( LHyp ` K )

  disjoint r z
  disjoint A r
  disjoint A z
  disjoint H r
  disjoint .\/ r
  disjoint .\/ z
  disjoint K r
  disjoint K z
  disjoint .<_ r
  disjoint .<_ z
  disjoint P r
  disjoint P z
  disjoint Q r
  disjoint Q z
  disjoint S r
  disjoint S z
  disjoint W r
  disjoint W z
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ S e. A ) /\ ( P =/= Q /\ -. S .<_ ( P .\/ Q ) /\ E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> E. z e. A ( -. z .<_ W /\ ( P .\/ z ) = ( S .\/ z ) ) )

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
    cS
    cA
    wcel
    #
    w3a
    #
    cP
    cQ
    wne
    #
    cS
    cP
    cQ
    c.or
    co
    c.le
    wbr
    wn
    #
    vr
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    cP
    @7
    c.or
    co
    cQ
    @7
    c.or
    co
    wceq
    #
    wa
    #
    vr
    cA
    wrex
    #
    w3a
    vz
    cv
    #
    cW
    c.le
    wbr
    wn
    cP
    @12
    c.or
    co
    cS
    @12
    c.or
    co
    wceq
    wa
    vz
    cA
    wrex
    #
    @0
    @4
    wa
    #
    @5
    @6
    @11
    @13
    @14
    @5
    @6
    @11
    @13
    wi
    @14
    @5
    @6
    w3a
    #
    @10
    @13
    vr
    cA
    @15
    @7
    cA
    wcel
    #
    @10
    w3a
    #
    @0
    @1
    @2
    @16
    @8
    wa
    @3
    @9
    @5
    @6
    @13
    @0
    @4
    @5
    @6
    @16
    @10
    simp11l
    @15
    @16
    @1
    @10
    @1
    @2
    @3
    @0
    @5
    @6
    simp1r1
    3ad2ant1
    @15
    @16
    @2
    @10
    @1
    @2
    @3
    @0
    @5
    @6
    simp1r2
    3ad2ant1
    @17
    @16
    @8
    @15
    @16
    @10
    simp2
    @15
    @16
    @8
    @9
    simp3l
    jca
    @15
    @16
    @3
    @10
    @1
    @2
    @3
    @0
    @5
    @6
    simp1r3
    3ad2ant1
    @15
    @16
    @8
    @9
    simp3r
    @14
    @5
    @6
    @16
    @10
    simp12
    @14
    @5
    @6
    @16
    @10
    simp13
    vz
    cA
    cP
    cQ
    @7
    cS
    cH
    c.or
    cK
    c.le
    cK
    cmee
    cfv
    #
    cW
    4that.l
    4that.j
    @18
    eqid
    4that.a
    4that.h
    4atexlemex6
    syl323anc
    rexlimdv3a
    3exp
    3impd
    3impia
end

include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cp0.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "co.mm"
include "wrex.mm"
include "simp1.mm"
include "simp21.mm"
include "simp22.mm"
include "simp32.mm"
include "simp31.mm"
include "simp23.mm"
include "simp33.mm"
include "4atex2-0aOLDN.mm"
include "syl133anc.mm"
include "eqcom.mm"
include "anbi2i.mm"
include "rexbii.mm"
include "sylibr.mm"

theorem 4atex2-0bOLDN
  let vz: setvar z
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cT: class T
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vr: setvar r
  let vy: setvar y
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
  disjoint T r
  disjoint T z
  disjoint A y
  disjoint H y
  disjoint .\/ y
  disjoint K y
  disjoint .<_ y
  disjoint P y
  disjoint Q y
  disjoint S y
  disjoint r y
  disjoint y z
  disjoint T y
  disjoint W y
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( P =/= Q /\ T = ( 0. ` K ) /\ E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> E. z e. A ( -. z .<_ W /\ ( S .\/ z ) = ( T .\/ z ) ) )

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
    cS
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    cP
    cQ
    wne
    #
    cT
    cK
    cp0
    cfv
    wceq
    #
    vr
    cv
    #
    cW
    c.le
    wbr
    wn
    cP
    @7
    c.or
    co
    cQ
    @7
    c.or
    co
    wceq
    wa
    vr
    cA
    wrex
    #
    w3a
    #
    w3a
    #
    vz
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    cT
    @11
    c.or
    co
    #
    cS
    @11
    c.or
    co
    #
    wceq
    #
    wa
    #
    vz
    cA
    wrex
    #
    @12
    @14
    @13
    wceq
    #
    wa
    #
    vz
    cA
    wrex
    @10
    @0
    @1
    @2
    @6
    @5
    @3
    @8
    @17
    @0
    @4
    @9
    simp1
    @0
    @1
    @2
    @3
    @9
    simp21
    @0
    @1
    @2
    @3
    @9
    simp22
    @0
    @4
    @5
    @6
    @8
    simp32
    @0
    @4
    @5
    @6
    @8
    simp31
    @0
    @1
    @2
    @3
    @9
    simp23
    @0
    @4
    @5
    @6
    @8
    simp33
    vz
    cA
    cP
    cQ
    cT
    cS
    cH
    c.or
    cK
    c.le
    cW
    vr
    4that.l
    4that.j
    4that.a
    4that.h
    4atex2-0aOLDN
    syl133anc
    @19
    @16
    vz
    cA
    @18
    @15
    @12
    @14
    @13
    eqcom
    anbi2i
    rexbii
    sylibr
end

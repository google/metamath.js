include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "simp1.mm"
include "simp2.mm"
include "simp31.mm"
include "simp32l.mm"
include "simp33.mm"
include "4atex2.mm"
include "syl113anc.mm"
include "clc.mm"
include "wb.mm"
include "simp1l.mm"
include "hlcvl.mm"
include "syl.mm"
include "adantr.mm"
include "simp23l.mm"
include "simpr.mm"
include "simp32r.mm"
include "cvlsupr2.mm"
include "syl131anc.mm"
include "anbi2d.mm"
include "rexbidva.mm"
include "mpbid.mm"

theorem 4atex3
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
  disjoint H z
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( P =/= Q /\ ( T e. A /\ S =/= T ) /\ E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> E. z e. A ( -. z .<_ W /\ ( z =/= S /\ z =/= T /\ z .<_ ( S .\/ T ) ) ) )

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
    cS
    cW
    c.le
    wbr
    wn
    #
    wa
    w3a
    #
    cP
    cQ
    wne
    #
    cT
    cA
    wcel
    #
    cS
    cT
    wne
    #
    wa
    #
    vr
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
    cQ
    @12
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
    cS
    @16
    c.or
    co
    cT
    @16
    c.or
    co
    wceq
    #
    wa
    #
    vz
    cA
    wrex
    #
    @17
    @16
    cS
    wne
    @16
    cT
    wne
    @16
    cS
    cT
    c.or
    co
    c.le
    wbr
    w3a
    #
    wa
    #
    vz
    cA
    wrex
    @15
    @2
    @7
    @8
    @9
    @13
    @20
    @2
    @7
    @14
    simp1
    @2
    @7
    @14
    simp2
    @2
    @7
    @8
    @11
    @13
    simp31
    @9
    @10
    @8
    @13
    @2
    @7
    simp32l
    #
    @2
    @7
    @8
    @11
    @13
    simp33
    vz
    cA
    cP
    cQ
    cS
    cT
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
    4atex2
    syl113anc
    @15
    @19
    @22
    vz
    cA
    @15
    @16
    cA
    wcel
    #
    wa
    #
    @18
    @21
    @17
    @25
    cK
    clc
    wcel
    #
    @5
    @9
    @24
    @10
    @18
    @21
    wb
    @15
    @26
    @24
    @15
    @0
    @26
    @0
    @1
    @7
    @14
    simp1l
    cK
    hlcvl
    syl
    adantr
    @15
    @5
    @24
    @5
    @6
    @3
    @4
    @2
    @14
    simp23l
    adantr
    @15
    @9
    @24
    @23
    adantr
    @15
    @24
    simpr
    @15
    @10
    @24
    @9
    @10
    @8
    @13
    @2
    @7
    simp32r
    adantr
    cA
    cS
    cT
    @16
    c.or
    cK
    c.le
    4that.a
    4that.l
    4that.j
    cvlsupr2
    syl131anc
    anbi2d
    rexbidva
    mpbid
end

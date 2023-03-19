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
include "oveq1.mm"
include "eqeq1d.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "simpl1.mm"
include "simpl23.mm"
include "simpl21.mm"
include "simpl32.mm"
include "simpr.mm"
include "simpl22.mm"
include "simp23l.mm"
include "adantr.mm"
include "simpl31.mm"
include "simpl33.mm"
include "4atex.mm"
include "syl132anc.mm"
include "eqcom.mm"
include "anbi2i.mm"
include "rexbii.mm"
include "sylib.mm"
include "simp1.mm"
include "simp21.mm"
include "simp22.mm"
include "simp32.mm"
include "simp31.mm"
include "simp33.mm"
include "pm2.61ne.mm"

theorem 4atex2
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( P =/= Q /\ T e. A /\ E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> E. z e. A ( -. z .<_ W /\ ( S .\/ z ) = ( T .\/ z ) ) )

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
    cS
    cW
    c.le
    wbr
    wn
    #
    wa
    #
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
    vr
    cv
    #
    cW
    c.le
    wbr
    wn
    cP
    @9
    c.or
    co
    cQ
    @9
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
    @13
    c.or
    co
    #
    cT
    @13
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
    @14
    cP
    @13
    c.or
    co
    #
    @16
    wceq
    #
    wa
    #
    vz
    cA
    wrex
    #
    cS
    cP
    cS
    cP
    wceq
    #
    @18
    @22
    vz
    cA
    @24
    @17
    @21
    @14
    @24
    @15
    @20
    @16
    cS
    cP
    @13
    c.or
    oveq1
    eqeq1d
    anbi2d
    rexbidv
    @12
    cS
    cP
    wne
    #
    wa
    #
    @0
    @5
    @1
    @8
    @25
    vy
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    cS
    @27
    c.or
    co
    #
    cP
    @27
    c.or
    co
    #
    wceq
    #
    wa
    #
    vy
    cA
    wrex
    #
    @19
    @0
    @6
    @11
    @25
    simpl1
    #
    @1
    @2
    @5
    @0
    @11
    @25
    simpl23
    @1
    @2
    @5
    @0
    @11
    @25
    simpl21
    #
    @7
    @8
    @10
    @0
    @6
    @25
    simpl32
    @12
    @25
    simpr
    @26
    @28
    @30
    @29
    wceq
    #
    wa
    #
    vy
    cA
    wrex
    #
    @33
    @26
    @0
    @1
    @2
    @3
    @7
    @10
    @38
    @34
    @35
    @1
    @2
    @5
    @0
    @11
    @25
    simpl22
    @12
    @3
    @25
    @3
    @4
    @1
    @2
    @0
    @11
    simp23l
    adantr
    @7
    @8
    @10
    @0
    @6
    @25
    simpl31
    @7
    @8
    @10
    @0
    @6
    @25
    simpl33
    vy
    cA
    cP
    cQ
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
    4atex
    syl132anc
    @37
    @32
    vy
    cA
    @36
    @31
    @28
    @30
    @29
    eqcom
    anbi2i
    rexbii
    sylib
    vz
    cA
    cS
    cP
    cT
    cH
    c.or
    cK
    c.le
    cW
    vy
    4that.l
    4that.j
    4that.a
    4that.h
    4atex
    syl132anc
    @12
    @0
    @1
    @2
    @8
    @7
    @10
    @23
    @0
    @6
    @11
    simp1
    @0
    @1
    @2
    @5
    @11
    simp21
    @0
    @1
    @2
    @5
    @11
    simp22
    @0
    @6
    @7
    @8
    @10
    simp32
    @0
    @6
    @7
    @8
    @10
    simp31
    @0
    @6
    @7
    @8
    @10
    simp33
    vz
    cA
    cP
    cQ
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
    4atex
    syl132anc
    pm2.61ne
end

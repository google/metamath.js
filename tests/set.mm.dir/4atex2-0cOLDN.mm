include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cp0.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wrex.mm"
include "simp21l.mm"
include "simp21r.mm"
include "simp23.mm"
include "oveq1d.mm"
include "simp32.mm"
include "eqtr4d.mm"
include "breq1.mm"
include "notbid.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"

theorem 4atex2-0cOLDN
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ S = ( 0. ` K ) ) /\ ( P =/= Q /\ T = ( 0. ` K ) /\ E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> E. z e. A ( -. z .<_ W /\ ( S .\/ z ) = ( T .\/ z ) ) )

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
    #
    cP
    cW
    c.le
    wbr
    #
    wn
    #
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
    cK
    cp0
    cfv
    #
    wceq
    #
    w3a
    #
    cP
    cQ
    wne
    #
    cT
    @6
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
    @11
    c.or
    co
    cQ
    @11
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
    @1
    @3
    cS
    cP
    c.or
    co
    #
    cT
    cP
    c.or
    co
    #
    wceq
    #
    vz
    cv
    #
    cW
    c.le
    wbr
    #
    wn
    #
    cS
    @18
    c.or
    co
    #
    cT
    @18
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
    @1
    @3
    @5
    @7
    @0
    @13
    simp21l
    @1
    @3
    @5
    @7
    @0
    @13
    simp21r
    @14
    @15
    @6
    cP
    c.or
    co
    @16
    @14
    cS
    @6
    cP
    c.or
    @0
    @4
    @5
    @7
    @13
    simp23
    oveq1d
    @14
    cT
    @6
    cP
    c.or
    @0
    @8
    @9
    @10
    @12
    simp32
    oveq1d
    eqtr4d
    @24
    @3
    @17
    wa
    vz
    cP
    cA
    @18
    cP
    wceq
    #
    @20
    @3
    @23
    @17
    @25
    @19
    @2
    @18
    cP
    cW
    c.le
    breq1
    notbid
    @25
    @21
    @15
    @22
    @16
    @18
    cP
    cS
    c.or
    oveq2
    @18
    cP
    cT
    c.or
    oveq2
    eqeq12d
    anbi12d
    rspcev
    syl12anc
end

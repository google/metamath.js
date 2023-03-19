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
include "simp32l.mm"
include "simp32r.mm"
include "col.mm"
include "cbs.mm"
include "simp1l.mm"
include "hlol.mm"
include "syl.mm"
include "eqid.mm"
include "atbase.mm"
include "olj02.mm"
include "syl2anc.mm"
include "simp23.mm"
include "oveq1d.mm"
include "hlatjidm.mm"
include "3eqtr4d.mm"
include "breq1.mm"
include "notbid.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"

theorem 4atex2-0aOLDN
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ S = ( 0. ` K ) ) /\ ( P =/= Q /\ ( T e. A /\ -. T .<_ W ) /\ E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> E. z e. A ( -. z .<_ W /\ ( S .\/ z ) = ( T .\/ z ) ) )

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
    cA
    wcel
    #
    cT
    cW
    c.le
    wbr
    #
    wn
    #
    wa
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
    @9
    @11
    cS
    cT
    c.or
    co
    #
    cT
    cT
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
    @19
    c.or
    co
    #
    cT
    @19
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
    @9
    @11
    @8
    @13
    @2
    @7
    simp32l
    #
    @9
    @11
    @8
    @13
    @2
    @7
    simp32r
    @15
    @5
    cT
    c.or
    co
    #
    cT
    @16
    @17
    @15
    cK
    col
    wcel
    #
    cT
    cK
    cbs
    cfv
    #
    wcel
    #
    @27
    cT
    wceq
    @15
    @0
    @28
    @0
    @1
    @7
    @14
    simp1l
    #
    cK
    hlol
    syl
    @15
    @9
    @30
    @26
    cA
    @29
    cT
    cK
    @29
    eqid
    #
    4that.a
    atbase
    syl
    @29
    c.or
    cK
    cT
    @5
    @32
    4that.j
    @5
    eqid
    olj02
    syl2anc
    @15
    cS
    @5
    cT
    c.or
    @2
    @3
    @4
    @6
    @14
    simp23
    oveq1d
    @15
    @0
    @9
    @17
    cT
    wceq
    @31
    @26
    cA
    c.or
    cK
    cT
    4that.j
    4that.a
    hlatjidm
    syl2anc
    3eqtr4d
    @25
    @11
    @18
    wa
    vz
    cT
    cA
    @19
    cT
    wceq
    #
    @21
    @11
    @24
    @18
    @33
    @20
    @10
    @19
    cT
    cW
    c.le
    breq1
    notbid
    @33
    @22
    @16
    @23
    @17
    @19
    cT
    cS
    c.or
    oveq2
    @19
    cT
    cT
    c.or
    oveq2
    eqeq12d
    anbi12d
    rspcev
    syl12anc
end

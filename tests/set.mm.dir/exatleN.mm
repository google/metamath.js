include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wceq.mm"
include "wne.mm"
include "simpl32.mm"
include "clat.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp122.mm"
include "atbase.mm"
include "simp121.mm"
include "simp123.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simp11r.mm"
include "3jca.mm"
include "simp2.mm"
include "simp133.mm"
include "hlatexch1.mm"
include "sylc.mm"
include "simp131.mm"
include "simp3.mm"
include "wb.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "lattrd.mm"
include "3expia.mm"
include "mtod.mm"
include "ex.mm"
include "necon4ad.mm"
include "simp31.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "impbid.mm"

theorem exatleN
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  assume atomle.b: |- B = ( Base ` K )
  assume atomle.l: |- .<_ = ( le ` K )
  assume atomle.j: |- .\/ = ( join ` K )
  assume atomle.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ X e. B ) /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( P .<_ X /\ -. Q .<_ X /\ R .<_ ( P .\/ Q ) ) ) -> ( R .<_ X <-> R = P ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    cR
    cA
    wcel
    #
    w3a
    #
    cP
    cX
    c.le
    wbr
    #
    cQ
    cX
    c.le
    wbr
    #
    wn
    #
    cR
    cP
    cQ
    c.or
    co
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    cR
    cX
    c.le
    wbr
    #
    cR
    cP
    wceq
    #
    @12
    @13
    cR
    cP
    @12
    cR
    cP
    wne
    #
    @13
    wn
    @12
    @15
    wa
    @13
    @8
    @7
    @9
    @10
    @2
    @6
    @15
    simpl32
    @12
    @15
    @13
    @8
    @12
    @15
    @13
    w3a
    #
    cB
    cK
    c.le
    cQ
    cP
    cR
    c.or
    co
    #
    cX
    atomle.b
    atomle.l
    @16
    @0
    cK
    clat
    wcel
    #
    @0
    @1
    @6
    @11
    @15
    @13
    simp11l
    #
    cK
    hllat
    syl
    #
    @16
    @4
    cQ
    cB
    wcel
    @3
    @4
    @5
    @2
    @11
    @15
    @13
    simp122
    #
    cA
    cB
    cQ
    cK
    atomle.b
    atomle.a
    atbase
    syl
    @16
    @18
    cP
    cB
    wcel
    #
    cR
    cB
    wcel
    #
    @17
    cB
    wcel
    @20
    @16
    @3
    @22
    @3
    @4
    @5
    @2
    @11
    @15
    @13
    simp121
    #
    cA
    cB
    cP
    cK
    atomle.b
    atomle.a
    atbase
    syl
    #
    @16
    @5
    @23
    @3
    @4
    @5
    @2
    @11
    @15
    @13
    simp123
    #
    cA
    cB
    cR
    cK
    atomle.b
    atomle.a
    atbase
    syl
    #
    cB
    c.or
    cK
    cP
    cR
    atomle.b
    atomle.j
    latjcl
    syl3anc
    @0
    @1
    @6
    @11
    @15
    @13
    simp11r
    #
    @16
    @0
    @5
    @4
    @3
    w3a
    #
    @15
    w3a
    @10
    cQ
    @17
    c.le
    wbr
    @16
    @0
    @29
    @15
    @19
    @16
    @5
    @4
    @3
    @26
    @21
    @24
    3jca
    @12
    @15
    @13
    simp2
    3jca
    @7
    @9
    @10
    @2
    @6
    @15
    @13
    simp133
    cA
    cR
    cQ
    cP
    c.or
    cK
    c.le
    atomle.l
    atomle.j
    atomle.a
    hlatexch1
    sylc
    @16
    @7
    @13
    @17
    cX
    c.le
    wbr
    #
    @7
    @9
    @10
    @2
    @6
    @15
    @13
    simp131
    @12
    @15
    @13
    simp3
    @16
    @18
    @22
    @23
    @1
    @7
    @13
    wa
    @30
    wb
    @20
    @25
    @27
    @28
    cB
    c.or
    cK
    c.le
    cP
    cR
    cX
    atomle.b
    atomle.l
    atomle.j
    latjle12
    syl13anc
    mpbi2and
    lattrd
    3expia
    mtod
    ex
    necon4ad
    @12
    @13
    @14
    @7
    @2
    @6
    @7
    @9
    @10
    simp31
    cR
    cP
    cX
    c.le
    breq1
    syl5ibrcom
    impbid
end

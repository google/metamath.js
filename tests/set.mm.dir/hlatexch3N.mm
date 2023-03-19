include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "simp1.mm"
include "simp21.mm"
include "simp22.mm"
include "eqid.mm"
include "hlatlej2.mm"
include "syl3anc.mm"
include "simp23.mm"
include "simp3r.mm"
include "breqtrrd.mm"
include "clat.mm"
include "cbs.mm"
include "wb.mm"
include "hllat.mm"
include "3ad2ant1.mm"
include "atbase.mm"
include "syl.mm"
include "hlatjcl.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "simp3l.mm"
include "ps-1.mm"
include "syl132anc.mm"
include "mpbid.mm"
include "eqcomd.mm"

theorem hlatexch3N
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  assume hlatexch4.j: |- .\/ = ( join ` K )
  assume hlatexch4.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( Q =/= R /\ ( P .\/ Q ) = ( P .\/ R ) ) ) -> ( P .\/ Q ) = ( Q .\/ R ) )

  proof
    cK
    chlt
    wcel
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
    cQ
    cR
    wne
    #
    cP
    cQ
    c.or
    co
    #
    cP
    cR
    c.or
    co
    #
    wceq
    #
    wa
    #
    w3a
    #
    cQ
    cR
    c.or
    co
    #
    @6
    @10
    @11
    @6
    cK
    cple
    cfv
    #
    wbr
    #
    @11
    @6
    wceq
    #
    @10
    cQ
    @6
    @12
    wbr
    #
    cR
    @6
    @12
    wbr
    #
    @13
    @10
    @0
    @1
    @2
    @15
    @0
    @4
    @9
    simp1
    #
    @0
    @1
    @2
    @3
    @9
    simp21
    #
    @0
    @1
    @2
    @3
    @9
    simp22
    #
    cA
    cP
    cQ
    c.or
    cK
    @12
    @12
    eqid
    #
    hlatexch4.j
    hlatexch4.a
    hlatlej2
    syl3anc
    @10
    cR
    @7
    @6
    @12
    @10
    @0
    @1
    @3
    cR
    @7
    @12
    wbr
    @17
    @18
    @0
    @1
    @2
    @3
    @9
    simp23
    #
    cA
    cP
    cR
    c.or
    cK
    @12
    @20
    hlatexch4.j
    hlatexch4.a
    hlatlej2
    syl3anc
    @0
    @4
    @5
    @8
    simp3r
    breqtrrd
    @10
    cK
    clat
    wcel
    #
    cQ
    cK
    cbs
    cfv
    #
    wcel
    #
    cR
    @23
    wcel
    #
    @6
    @23
    wcel
    #
    @15
    @16
    wa
    @13
    wb
    @0
    @4
    @22
    @9
    cK
    hllat
    3ad2ant1
    @10
    @2
    @24
    @19
    cA
    @23
    cQ
    cK
    @23
    eqid
    #
    hlatexch4.a
    atbase
    syl
    @10
    @3
    @25
    @21
    cA
    @23
    cR
    cK
    @27
    hlatexch4.a
    atbase
    syl
    @10
    @0
    @1
    @2
    @26
    @17
    @18
    @19
    cA
    @23
    c.or
    cK
    cP
    cQ
    @27
    hlatexch4.j
    hlatexch4.a
    hlatjcl
    syl3anc
    @23
    c.or
    cK
    @12
    cQ
    cR
    @6
    @27
    @20
    hlatexch4.j
    latjle12
    syl13anc
    mpbi2and
    @10
    @0
    @2
    @3
    @5
    @1
    @2
    @13
    @14
    wb
    @17
    @19
    @21
    @0
    @4
    @5
    @8
    simp3l
    @18
    @19
    cA
    cQ
    cR
    cP
    cQ
    c.or
    cK
    @12
    @20
    hlatexch4.j
    hlatexch4.a
    ps-1
    syl132anc
    mpbid
    eqcomd
end

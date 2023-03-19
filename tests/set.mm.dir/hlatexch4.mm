include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "simp11.mm"
include "simp2l.mm"
include "simp2r.mm"
include "eqid.mm"
include "hlatlej2.mm"
include "syl3anc.mm"
include "simp33.mm"
include "breqtrrd.mm"
include "wi.mm"
include "simp12.mm"
include "simp13.mm"
include "simp32.mm"
include "necomd.mm"
include "hlatexch2.mm"
include "syl131anc.mm"
include "mpd.mm"
include "hlatjcom.mm"
include "breqtrd.mm"
include "clat.mm"
include "cbs.mm"
include "wb.mm"
include "hllat.mm"
include "syl.mm"
include "atbase.mm"
include "hlatjcl.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "simp31.mm"
include "ps-1.mm"
include "syl132anc.mm"
include "mpbid.mm"

theorem hlatexch4
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.or: class .\/
  let cK: class K
  assume hlatexch4.j: |- .\/ = ( join ` K )
  assume hlatexch4.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A ) /\ ( P =/= R /\ Q =/= S /\ ( P .\/ Q ) = ( R .\/ S ) ) ) -> ( P .\/ R ) = ( Q .\/ S ) )

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
    w3a
    #
    cR
    cA
    wcel
    #
    cS
    cA
    wcel
    #
    wa
    #
    cP
    cR
    wne
    #
    cQ
    cS
    wne
    #
    cP
    cQ
    c.or
    co
    #
    cR
    cS
    c.or
    co
    #
    wceq
    #
    w3a
    #
    w3a
    #
    cP
    cR
    c.or
    co
    #
    cQ
    cS
    c.or
    co
    #
    cK
    cple
    cfv
    #
    wbr
    #
    @14
    @15
    wceq
    #
    @13
    cP
    @15
    @16
    wbr
    #
    cR
    @15
    @16
    wbr
    #
    @17
    @13
    cP
    cS
    cQ
    c.or
    co
    #
    @15
    @16
    @13
    cS
    @9
    @16
    wbr
    #
    cP
    @21
    @16
    wbr
    #
    @13
    cS
    @10
    @9
    @16
    @13
    @0
    @4
    @5
    cS
    @10
    @16
    wbr
    @0
    @1
    @2
    @6
    @12
    simp11
    #
    @3
    @4
    @5
    @12
    simp2l
    #
    @3
    @4
    @5
    @12
    simp2r
    #
    cA
    cR
    cS
    c.or
    cK
    @16
    @16
    eqid
    #
    hlatexch4.j
    hlatexch4.a
    hlatlej2
    syl3anc
    @3
    @6
    @7
    @8
    @11
    simp33
    #
    breqtrrd
    @13
    @0
    @5
    @1
    @2
    cS
    cQ
    wne
    @22
    @23
    wi
    @24
    @26
    @0
    @1
    @2
    @6
    @12
    simp12
    #
    @0
    @1
    @2
    @6
    @12
    simp13
    #
    @13
    cQ
    cS
    @3
    @6
    @7
    @8
    @11
    simp32
    #
    necomd
    cA
    cS
    cP
    cQ
    c.or
    cK
    @16
    @27
    hlatexch4.j
    hlatexch4.a
    hlatexch2
    syl131anc
    mpd
    @13
    @0
    @5
    @2
    @21
    @15
    wceq
    @24
    @26
    @30
    cA
    c.or
    cK
    cS
    cQ
    hlatexch4.j
    hlatexch4.a
    hlatjcom
    syl3anc
    breqtrd
    @13
    cQ
    @10
    @16
    wbr
    #
    @20
    @13
    cQ
    @9
    @10
    @16
    @13
    @0
    @1
    @2
    cQ
    @9
    @16
    wbr
    @24
    @29
    @30
    cA
    cP
    cQ
    c.or
    cK
    @16
    @27
    hlatexch4.j
    hlatexch4.a
    hlatlej2
    syl3anc
    @28
    breqtrd
    @13
    @0
    @2
    @4
    @5
    @8
    @32
    @20
    wi
    @24
    @30
    @25
    @26
    @31
    cA
    cQ
    cR
    cS
    c.or
    cK
    @16
    @27
    hlatexch4.j
    hlatexch4.a
    hlatexch2
    syl131anc
    mpd
    @13
    cK
    clat
    wcel
    #
    cP
    cK
    cbs
    cfv
    #
    wcel
    #
    cR
    @34
    wcel
    #
    @15
    @34
    wcel
    #
    @19
    @20
    wa
    @17
    wb
    @13
    @0
    @33
    @24
    cK
    hllat
    syl
    @13
    @1
    @35
    @29
    cA
    @34
    cP
    cK
    @34
    eqid
    #
    hlatexch4.a
    atbase
    syl
    @13
    @4
    @36
    @25
    cA
    @34
    cR
    cK
    @38
    hlatexch4.a
    atbase
    syl
    @13
    @0
    @2
    @5
    @37
    @24
    @30
    @26
    cA
    @34
    c.or
    cK
    cQ
    cS
    @38
    hlatexch4.j
    hlatexch4.a
    hlatjcl
    syl3anc
    @34
    c.or
    cK
    @16
    cP
    cR
    @15
    @38
    @27
    hlatexch4.j
    latjle12
    syl13anc
    mpbi2and
    @13
    @0
    @1
    @4
    @7
    @2
    @5
    @17
    @18
    wb
    @24
    @29
    @25
    @3
    @6
    @7
    @8
    @11
    simp31
    @30
    @26
    cA
    cP
    cR
    cQ
    cS
    c.or
    cK
    @16
    @27
    hlatexch4.j
    hlatexch4.a
    ps-1
    syl132anc
    mpbid
end

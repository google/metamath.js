include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wne.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "oveq1.mm"
include "hlatjidm.mm"
include "3ad2antr2.mm"
include "sylan9eqr.mm"
include "oveq1d.mm"
include "simpll.mm"
include "simplr2.mm"
include "simplr3.mm"
include "2atnelpln.mm"
include "syl3anc.mm"
include "eqneltrd.mm"
include "ex.mm"
include "necon2ad.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "wb.mm"
include "hllat.mm"
include "adantr.mm"
include "simpr3.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "hlatjcl.mm"
include "3adant3r3.mm"
include "latleeqj2.mm"
include "eleq1.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "sylbid.mm"
include "con2d.mm"
include "jcad.mm"
include "lplni2.mm"
include "3expia.mm"
include "impbid.mm"

theorem islpln2a
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  assume islpln2a.l: |- .<_ = ( le ` K )
  assume islpln2a.j: |- .\/ = ( join ` K )
  assume islpln2a.a: |- A = ( Atoms ` K )
  assume islpln2a.p: |- P = ( LPlanes ` K )


  assert |- ( ( K e. HL /\ ( Q e. A /\ R e. A /\ S e. A ) ) -> ( ( ( Q .\/ R ) .\/ S ) e. P <-> ( Q =/= R /\ -. S .<_ ( Q .\/ R ) ) ) )

  proof
    cK
    chlt
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
    cS
    cA
    wcel
    #
    w3a
    #
    wa
    #
    cQ
    cR
    c.or
    co
    #
    cS
    c.or
    co
    #
    cP
    wcel
    #
    cQ
    cR
    wne
    #
    cS
    @6
    c.le
    wbr
    #
    wn
    #
    wa
    #
    @5
    @8
    @9
    @11
    @5
    @8
    cQ
    cR
    @5
    cQ
    cR
    wceq
    #
    @8
    wn
    #
    @5
    @13
    wa
    #
    @7
    cR
    cS
    c.or
    co
    #
    cP
    @15
    @6
    cR
    cS
    c.or
    @13
    @5
    @6
    cR
    cR
    c.or
    co
    #
    cR
    cQ
    cR
    cR
    c.or
    oveq1
    @0
    @1
    @2
    @17
    cR
    wceq
    @3
    cA
    c.or
    cK
    cR
    islpln2a.j
    islpln2a.a
    hlatjidm
    3ad2antr2
    sylan9eqr
    oveq1d
    @15
    @0
    @2
    @3
    @16
    cP
    wcel
    wn
    @0
    @4
    @13
    simpll
    @1
    @2
    @3
    @0
    @13
    simplr2
    @1
    @2
    @3
    @0
    @13
    simplr3
    cA
    cP
    cR
    cS
    c.or
    cK
    islpln2a.j
    islpln2a.a
    islpln2a.p
    2atnelpln
    syl3anc
    eqneltrd
    ex
    necon2ad
    @5
    @10
    @8
    @5
    @10
    @7
    @6
    wceq
    #
    @14
    @5
    cK
    clat
    wcel
    #
    cS
    cK
    cbs
    cfv
    #
    wcel
    #
    @6
    @20
    wcel
    #
    @10
    @18
    wb
    @0
    @19
    @4
    cK
    hllat
    adantr
    @5
    @3
    @21
    @0
    @1
    @2
    @3
    simpr3
    cA
    @20
    cS
    cK
    @20
    eqid
    #
    islpln2a.a
    atbase
    syl
    @0
    @1
    @2
    @22
    @3
    cA
    @20
    c.or
    cK
    cQ
    cR
    @23
    islpln2a.j
    islpln2a.a
    hlatjcl
    3adant3r3
    @20
    c.or
    cK
    c.le
    cS
    @6
    @23
    islpln2a.l
    islpln2a.j
    latleeqj2
    syl3anc
    @5
    @14
    @18
    @6
    cP
    wcel
    #
    wn
    #
    @0
    @1
    @2
    @25
    @3
    cA
    cP
    cQ
    cR
    c.or
    cK
    islpln2a.j
    islpln2a.a
    islpln2a.p
    2atnelpln
    3adant3r3
    @18
    @8
    @24
    @7
    @6
    cP
    eleq1
    notbid
    syl5ibrcom
    sylbid
    con2d
    jcad
    @0
    @4
    @12
    @8
    cA
    cP
    cQ
    cR
    cS
    c.or
    cK
    c.le
    islpln2a.l
    islpln2a.j
    islpln2a.a
    islpln2a.p
    lplni2
    3expia
    impbid
end

include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wne.mm"
include "wceq.mm"
include "cmee.mm"
include "cfv.mm"
include "simpl33.mm"
include "simpr.mm"
include "clat.mm"
include "wb.mm"
include "simpl11.mm"
include "hllat.mm"
include "syl.mm"
include "simpl2l.mm"
include "atbase.mm"
include "simpl1.mm"
include "hlatjcl.mm"
include "simpl2r.mm"
include "eqid.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "simpl12.mm"
include "simpl13.mm"
include "simpl31.mm"
include "simpl32.mm"
include "2atjm.mm"
include "syl132anc.mm"
include "breqtrd.mm"
include "cal.mm"
include "hlatl.mm"
include "atcmp.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "ex.mm"
include "necon3ad.mm"
include "wi.mm"
include "simp31.mm"
include "nbrne2.mm"
include "necomd.mm"
include "impbid.mm"

theorem atbtwn
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  assume atbtwn.b: |- B = ( Base ` K )
  assume atbtwn.l: |- .<_ = ( le ` K )
  assume atbtwn.j: |- .\/ = ( join ` K )
  assume atbtwn.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ X e. B ) /\ ( P .<_ X /\ -. Q .<_ X /\ R .<_ ( P .\/ Q ) ) ) -> ( R =/= P <-> -. R .<_ X ) )

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
    cX
    cB
    wcel
    #
    wa
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
    wn
    #
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    cR
    cP
    wne
    #
    cR
    cX
    c.le
    wbr
    #
    wn
    #
    @12
    @14
    cR
    cP
    @12
    @14
    cR
    cP
    wceq
    #
    @12
    @14
    wa
    #
    cR
    cP
    c.le
    wbr
    #
    @16
    @17
    cR
    @9
    cX
    cK
    cmee
    cfv
    #
    co
    #
    cP
    c.le
    @17
    @10
    @14
    cR
    @20
    c.le
    wbr
    #
    @7
    @8
    @10
    @3
    @6
    @14
    simpl33
    @12
    @14
    simpr
    @17
    cK
    clat
    wcel
    #
    cR
    cB
    wcel
    #
    @9
    cB
    wcel
    #
    @5
    @10
    @14
    wa
    @21
    wb
    @17
    @0
    @22
    @0
    @1
    @2
    @6
    @11
    @14
    simpl11
    #
    cK
    hllat
    syl
    @17
    @4
    @23
    @4
    @5
    @3
    @11
    @14
    simpl2l
    #
    cA
    cB
    cR
    cK
    atbtwn.b
    atbtwn.a
    atbase
    syl
    @17
    @3
    @24
    @3
    @6
    @11
    @14
    simpl1
    cA
    cB
    c.or
    cK
    cP
    cQ
    atbtwn.b
    atbtwn.j
    atbtwn.a
    hlatjcl
    syl
    @4
    @5
    @3
    @11
    @14
    simpl2r
    #
    cB
    cK
    c.le
    @19
    cR
    @9
    cX
    atbtwn.b
    atbtwn.l
    @19
    eqid
    #
    latlem12
    syl13anc
    mpbi2and
    @17
    @0
    @1
    @2
    @5
    @7
    @8
    @20
    cP
    wceq
    @25
    @0
    @1
    @2
    @6
    @11
    @14
    simpl12
    #
    @0
    @1
    @2
    @6
    @11
    @14
    simpl13
    @27
    @7
    @8
    @10
    @3
    @6
    @14
    simpl31
    @7
    @8
    @10
    @3
    @6
    @14
    simpl32
    cA
    cB
    cP
    cQ
    c.or
    cK
    c.le
    @19
    cX
    atbtwn.b
    atbtwn.l
    atbtwn.j
    @28
    atbtwn.a
    2atjm
    syl132anc
    breqtrd
    @17
    cK
    cal
    wcel
    #
    @4
    @1
    @18
    @16
    wb
    @17
    @0
    @30
    @25
    cK
    hlatl
    syl
    @26
    @29
    cA
    cR
    cP
    cK
    c.le
    atbtwn.l
    atbtwn.a
    atcmp
    syl3anc
    mpbid
    ex
    necon3ad
    @12
    @7
    @15
    @13
    wi
    @3
    @6
    @7
    @8
    @10
    simp31
    @7
    @15
    @13
    @7
    @15
    wa
    cP
    cR
    cP
    cR
    cX
    c.le
    nbrne2
    necomd
    ex
    syl
    impbid
end

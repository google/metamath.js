include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wn.mm"
include "wa.mm"
include "cp0.mm"
include "cfv.mm"
include "ccvr.mm"
include "wbr.mm"
include "simpl1.mm"
include "simpl2.mm"
include "eqid.mm"
include "atcvr0.mm"
include "syl2anc.mm"
include "atcvr1.mm"
include "biimpa.mm"
include "cbs.mm"
include "wi.mm"
include "cops.mm"
include "hlop.mm"
include "op0cl.mm"
include "3syl.mm"
include "atbase.mm"
include "syl.mm"
include "clat.mm"
include "hllat.mm"
include "simpl3.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "cvrntr.mm"
include "syl13anc.mm"
include "mp2and.mm"
include "simpll1.mm"
include "sylancom.mm"
include "mtand.mm"
include "ex.mm"
include "wceq.mm"
include "hlatjidm.mm"
include "3adant3.mm"
include "simp2.mm"
include "eqeltrd.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "syl5ibcom.mm"
include "necon3bd.mm"
include "impbid.mm"

theorem lnnat
  let cA: class A
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  assume lnnat.j: |- .\/ = ( join ` K )
  assume lnnat.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ P e. A /\ Q e. A ) -> ( P =/= Q <-> -. ( P .\/ Q ) e. A ) )

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
    cP
    cQ
    wne
    #
    cP
    cQ
    c.or
    co
    #
    cA
    wcel
    #
    wn
    #
    @3
    @4
    @7
    @3
    @4
    wa
    #
    @6
    cK
    cp0
    cfv
    #
    @5
    cK
    ccvr
    cfv
    #
    wbr
    #
    @8
    @9
    cP
    @10
    wbr
    #
    cP
    @5
    @10
    wbr
    #
    @11
    wn
    #
    @8
    @0
    @1
    @12
    @0
    @1
    @2
    @4
    simpl1
    #
    @0
    @1
    @2
    @4
    simpl2
    #
    cA
    @10
    chlt
    cP
    cK
    @9
    @9
    eqid
    #
    @10
    eqid
    #
    lnnat.a
    atcvr0
    syl2anc
    @3
    @4
    @13
    cA
    @10
    cP
    cQ
    c.or
    cK
    lnnat.j
    @18
    lnnat.a
    atcvr1
    biimpa
    @8
    @0
    @9
    cK
    cbs
    cfv
    #
    wcel
    #
    cP
    @19
    wcel
    #
    @5
    @19
    wcel
    #
    @12
    @13
    wa
    @14
    wi
    @15
    @8
    @0
    cK
    cops
    wcel
    @20
    @15
    cK
    hlop
    @19
    cK
    @9
    @19
    eqid
    #
    @17
    op0cl
    3syl
    @8
    @1
    @21
    @16
    cA
    @19
    cP
    cK
    @23
    lnnat.a
    atbase
    syl
    #
    @8
    cK
    clat
    wcel
    #
    @21
    cQ
    @19
    wcel
    #
    @22
    @8
    @0
    @25
    @15
    cK
    hllat
    syl
    @24
    @8
    @2
    @26
    @0
    @1
    @2
    @4
    simpl3
    cA
    @19
    cQ
    cK
    @23
    lnnat.a
    atbase
    syl
    @19
    c.or
    cK
    cP
    cQ
    @23
    lnnat.j
    latjcl
    syl3anc
    chlt
    @19
    @10
    cK
    @9
    cP
    @5
    @23
    @18
    cvrntr
    syl13anc
    mp2and
    @8
    @6
    @0
    @11
    @0
    @1
    @2
    @4
    @6
    simpll1
    cA
    @10
    chlt
    @5
    cK
    @9
    @17
    @18
    lnnat.a
    atcvr0
    sylancom
    mtand
    ex
    @3
    @6
    cP
    cQ
    @3
    cP
    cP
    c.or
    co
    #
    cA
    wcel
    cP
    cQ
    wceq
    #
    @6
    @3
    @27
    cP
    cA
    @0
    @1
    @27
    cP
    wceq
    @2
    cA
    c.or
    cK
    cP
    lnnat.j
    lnnat.a
    hlatjidm
    3adant3
    @0
    @1
    @2
    simp2
    eqeltrd
    @28
    @27
    @5
    cA
    cP
    cQ
    cP
    c.or
    oveq2
    eleq1d
    syl5ibcom
    necon3bd
    impbid
end

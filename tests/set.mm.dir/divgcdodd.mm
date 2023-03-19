include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "c2.mm"
include "cgcd.mm"
include "co.mm"
include "cdiv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wi.mm"
include "wo.mm"
include "c1.mm"
include "n2dvds1.mm"
include "cz.mm"
include "wb.mm"
include "2z.mm"
include "nnz.mm"
include "gcddvds.mm"
include "syl2an.mm"
include "simpld.mm"
include "cc0.mm"
include "wne.mm"
include "gcdnncl.mm"
include "nnzd.mm"
include "nnne0d.mm"
include "adantr.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "simprd.mm"
include "adantl.mm"
include "dvdsgcdb.mm"
include "mp3an2i.mm"
include "wceq.mm"
include "gcddiv.mm"
include "syl31anc.mm"
include "nncnd.mm"
include "dividd.mm"
include "eqtr3d.mm"
include "breq2d.mm"
include "biimpd.mm"
include "sylbid.mm"
include "expdimp.mm"
include "mtoi.mm"
include "ex.mm"
include "imor.mm"
include "sylib.mm"

theorem divgcdodd
  let cA: class A
  let cB: class B


  assert |- ( ( A e. NN /\ B e. NN ) -> ( -. 2 || ( A / ( A gcd B ) ) \/ -. 2 || ( B / ( A gcd B ) ) ) )

  proof
    cA
    cn
    wcel
    #
    cB
    cn
    wcel
    #
    wa
    #
    c2
    cA
    cA
    cB
    cgcd
    co
    #
    cdiv
    co
    #
    cdvds
    wbr
    #
    c2
    cB
    @3
    cdiv
    co
    #
    cdvds
    wbr
    #
    wn
    #
    wi
    @5
    wn
    @8
    wo
    @2
    @5
    @8
    @2
    @5
    wa
    @7
    c2
    c1
    cdvds
    wbr
    #
    n2dvds1
    @2
    @5
    @7
    @9
    @2
    @5
    @7
    wa
    #
    c2
    @4
    @6
    cgcd
    co
    #
    cdvds
    wbr
    #
    @9
    c2
    cz
    wcel
    @2
    @4
    cz
    wcel
    #
    @6
    cz
    wcel
    #
    @10
    @12
    wb
    2z
    @2
    @3
    cA
    cdvds
    wbr
    #
    @13
    @2
    @15
    @3
    cB
    cdvds
    wbr
    #
    @0
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    @15
    @16
    wa
    #
    @1
    cA
    nnz
    #
    cB
    nnz
    #
    cA
    cB
    gcddvds
    syl2an
    #
    simpld
    @2
    @3
    cz
    wcel
    #
    @3
    cc0
    wne
    #
    @17
    @15
    @13
    wb
    @2
    @3
    cA
    cB
    gcdnncl
    #
    nnzd
    #
    @2
    @3
    @25
    nnne0d
    #
    @0
    @17
    @1
    @20
    adantr
    #
    @3
    cA
    dvdsval2
    syl3anc
    mpbid
    @2
    @16
    @14
    @2
    @15
    @16
    @22
    simprd
    @2
    @23
    @24
    @18
    @16
    @14
    wb
    @26
    @27
    @1
    @18
    @0
    @21
    adantl
    #
    @3
    cB
    dvdsval2
    syl3anc
    mpbid
    c2
    @4
    @6
    dvdsgcdb
    mp3an2i
    @2
    @12
    @9
    @2
    @11
    c1
    c2
    cdvds
    @2
    @3
    @3
    cdiv
    co
    #
    @11
    c1
    @2
    @17
    @18
    @3
    cn
    wcel
    @19
    @30
    @11
    wceq
    @28
    @29
    @25
    @22
    cA
    cB
    @3
    gcddiv
    syl31anc
    @2
    @3
    @2
    @3
    @25
    nncnd
    @27
    dividd
    eqtr3d
    breq2d
    biimpd
    sylbid
    expdimp
    mtoi
    ex
    @5
    @8
    imor
    sylib
end

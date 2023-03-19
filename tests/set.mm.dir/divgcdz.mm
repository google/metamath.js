include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cgcd.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cdiv.mm"
include "wa.mm"
include "gcddvds.mm"
include "3adant3.mm"
include "simpld.mm"
include "wb.mm"
include "cn.mm"
include "gcd2n0cl.mm"
include "nnz.mm"
include "nnne0.mm"
include "jca.mm"
include "syl.mm"
include "simp1.mm"
include "df-3an.mm"
include "sylanbrc.mm"
include "dvdsval2.mm"
include "mpbid.mm"

theorem divgcdz
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ZZ /\ B e. ZZ /\ B =/= 0 ) -> ( A / ( A gcd B ) ) e. ZZ )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    cB
    cc0
    wne
    #
    w3a
    #
    cA
    cB
    cgcd
    co
    #
    cA
    cdvds
    wbr
    #
    cA
    @4
    cdiv
    co
    cz
    wcel
    #
    @3
    @5
    @4
    cB
    cdvds
    wbr
    #
    @0
    @1
    @5
    @7
    wa
    @2
    cA
    cB
    gcddvds
    3adant3
    simpld
    @3
    @4
    cz
    wcel
    #
    @4
    cc0
    wne
    #
    @0
    w3a
    #
    @5
    @6
    wb
    @3
    @8
    @9
    wa
    #
    @0
    @10
    @3
    @4
    cn
    wcel
    #
    @11
    cA
    cB
    gcd2n0cl
    @12
    @8
    @9
    @4
    nnz
    @4
    nnne0
    jca
    syl
    @0
    @1
    @2
    simp1
    @8
    @9
    @0
    df-3an
    sylanbrc
    @4
    cA
    dvdsval2
    syl
    mpbid
end

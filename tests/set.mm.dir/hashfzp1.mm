include "wceq.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "chash.mm"
include "cmin.mm"
include "wi.mm"
include "c0.mm"
include "cc0.mm"
include "hash0.mm"
include "clt.mm"
include "wbr.mm"
include "eluzelre.mm"
include "ltp1d.mm"
include "cz.mm"
include "wa.mm"
include "wb.mm"
include "eluzelz.mm"
include "peano2z.mm"
include "ancri.mm"
include "fzn.mm"
include "3syl.mm"
include "mpbid.mm"
include "fveq2d.mm"
include "zcnd.mm"
include "subidd.mm"
include "3eqtr4a.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "syl5ibr.mm"
include "wn.mm"
include "wo.mm"
include "uzp1.mm"
include "pm2.24.mm"
include "eqcoms.mm"
include "ax-1.mm"
include "jaoi.mm"
include "syl.mm"
include "impcom.mm"
include "hashfz.mm"
include "eluzel2.mm"
include "1cnd.mm"
include "nppcan2d.mm"
include "adantl.mm"
include "eqtrd.mm"
include "ex.mm"
include "pm2.61i.mm"

theorem hashfzp1
  let cA: class A
  let cB: class B


  assert |- ( B e. ( ZZ>= ` A ) -> ( # ` ( ( A + 1 ) ... B ) ) = ( B - A ) )

  proof
    cA
    cB
    wceq
    #
    cB
    cA
    cuz
    cfv
    wcel
    #
    cA
    c1
    caddc
    co
    #
    cB
    cfz
    co
    #
    chash
    cfv
    #
    cB
    cA
    cmin
    co
    #
    wceq
    #
    wi
    @1
    @6
    @0
    cB
    c1
    caddc
    co
    #
    cB
    cfz
    co
    #
    chash
    cfv
    #
    cB
    cB
    cmin
    co
    #
    wceq
    @1
    c0
    chash
    cfv
    cc0
    @9
    @10
    hash0
    @1
    @8
    c0
    chash
    @1
    cB
    @7
    clt
    wbr
    #
    @8
    c0
    wceq
    #
    @1
    cB
    cA
    cB
    eluzelre
    ltp1d
    @1
    cB
    cz
    wcel
    #
    @7
    cz
    wcel
    #
    @13
    wa
    @11
    @12
    wb
    cA
    cB
    eluzelz
    #
    @13
    @14
    cB
    peano2z
    ancri
    @7
    cB
    fzn
    3syl
    mpbid
    fveq2d
    @1
    cB
    @1
    cB
    @15
    zcnd
    #
    subidd
    3eqtr4a
    @0
    @4
    @9
    @5
    @10
    @0
    @3
    @8
    chash
    @0
    @2
    @7
    cB
    cfz
    cA
    cB
    c1
    caddc
    oveq1
    oveq1d
    fveq2d
    cA
    cB
    cB
    cmin
    oveq2
    eqeq12d
    syl5ibr
    @0
    wn
    #
    @1
    @6
    @17
    @1
    wa
    #
    @4
    cB
    @2
    cmin
    co
    c1
    caddc
    co
    #
    @5
    @18
    cB
    @2
    cuz
    cfv
    wcel
    #
    @4
    @19
    wceq
    @1
    @17
    @20
    @1
    cB
    cA
    wceq
    #
    @20
    wo
    @17
    @20
    wi
    #
    cA
    cB
    uzp1
    @21
    @22
    @20
    @22
    cA
    cB
    @0
    @20
    pm2.24
    eqcoms
    @20
    @17
    ax-1
    jaoi
    syl
    impcom
    @2
    cB
    hashfz
    syl
    @1
    @19
    @5
    wceq
    @17
    @1
    cB
    cA
    c1
    @16
    @1
    cA
    cA
    cB
    eluzel2
    zcnd
    @1
    1cnd
    nppcan2d
    adantl
    eqtrd
    ex
    pm2.61i
end

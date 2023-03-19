include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "cfzo.mm"
include "co.mm"
include "chash.mm"
include "cmin.mm"
include "c1.mm"
include "cc0.mm"
include "eluzel2.mm"
include "zcnd.mm"
include "subidd.mm"
include "c0.mm"
include "fzo0.mm"
include "fveq2i.mm"
include "hash0.mm"
include "eqtri.mm"
include "syl6reqr.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "wa.mm"
include "cfz.mm"
include "cz.mm"
include "eluzelz.mm"
include "fzoval.mm"
include "syl.mm"
include "adantr.mm"
include "caddc.mm"
include "hashfz.mm"
include "1cnd.mm"
include "sub32d.mm"
include "oveq1d.mm"
include "cc.mm"
include "subcld.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "eqtrd.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "uzm1.mm"
include "mpjaod.mm"

theorem hashfzo
  let cA: class A
  let cB: class B


  assert |- ( B e. ( ZZ>= ` A ) -> ( # ` ( A ..^ B ) ) = ( B - A ) )

  proof
    cB
    cA
    cuz
    cfv
    #
    wcel
    #
    cB
    cA
    wceq
    #
    cA
    cB
    cfzo
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
    cB
    c1
    cmin
    co
    #
    @0
    wcel
    #
    @1
    @6
    @2
    cA
    cA
    cfzo
    co
    #
    chash
    cfv
    #
    cA
    cA
    cmin
    co
    #
    wceq
    @1
    @11
    cc0
    @10
    @1
    cA
    @1
    cA
    cA
    cB
    eluzel2
    zcnd
    #
    subidd
    @10
    c0
    chash
    cfv
    cc0
    @9
    c0
    chash
    cA
    fzo0
    fveq2i
    hash0
    eqtri
    syl6reqr
    @2
    @4
    @10
    @5
    @11
    @2
    @3
    @9
    chash
    cB
    cA
    cA
    cfzo
    oveq2
    fveq2d
    cB
    cA
    cA
    cmin
    oveq1
    eqeq12d
    syl5ibrcom
    @1
    @8
    @6
    @1
    @8
    wa
    @4
    cA
    @7
    cfz
    co
    #
    chash
    cfv
    #
    @5
    @1
    @4
    @14
    wceq
    @8
    @1
    @3
    @13
    chash
    @1
    cB
    cz
    wcel
    @3
    @13
    wceq
    cA
    cB
    eluzelz
    #
    cA
    cB
    fzoval
    syl
    fveq2d
    adantr
    @8
    @1
    @14
    @7
    cA
    cmin
    co
    #
    c1
    caddc
    co
    #
    @5
    cA
    @7
    hashfz
    @1
    @17
    @5
    c1
    cmin
    co
    #
    c1
    caddc
    co
    #
    @5
    @1
    @16
    @18
    c1
    caddc
    @1
    cB
    c1
    cA
    @1
    cB
    @15
    zcnd
    #
    @1
    1cnd
    @12
    sub32d
    oveq1d
    @1
    @5
    cc
    wcel
    c1
    cc
    wcel
    @19
    @5
    wceq
    @1
    cB
    cA
    @20
    @12
    subcld
    ax-1cn
    @5
    c1
    npcan
    sylancl
    eqtrd
    sylan9eqr
    eqtrd
    ex
    cA
    cB
    uzm1
    mpjaod
end

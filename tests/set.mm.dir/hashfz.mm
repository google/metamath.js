include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cfz.mm"
include "co.mm"
include "chash.mm"
include "c1.mm"
include "cmin.mm"
include "caddc.mm"
include "cen.mm"
include "wbr.mm"
include "wceq.mm"
include "cz.mm"
include "eluzel2.mm"
include "eluzelz.mm"
include "1z.mm"
include "zsubcl.mm"
include "sylancr.mm"
include "fzen.mm"
include "syl3anc.mm"
include "cc.mm"
include "zcnd.mm"
include "ax-1cn.mm"
include "pncan3.mm"
include "sylancl.mm"
include "1cnd.mm"
include "addsub12d.mm"
include "subcld.mm"
include "addcom.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "breqtrd.mm"
include "hasheni.mm"
include "syl.mm"
include "cn0.mm"
include "uznn0sub.mm"
include "peano2nn0.mm"
include "hashfz1.mm"
include "3syl.mm"

theorem hashfz
  let cA: class A
  let cB: class B


  assert |- ( B e. ( ZZ>= ` A ) -> ( # ` ( A ... B ) ) = ( ( B - A ) + 1 ) )

  proof
    cB
    cA
    cuz
    cfv
    wcel
    #
    cA
    cB
    cfz
    co
    #
    chash
    cfv
    #
    c1
    cB
    cA
    cmin
    co
    #
    c1
    caddc
    co
    #
    cfz
    co
    #
    chash
    cfv
    #
    @4
    @0
    @1
    @5
    cen
    wbr
    @2
    @6
    wceq
    @0
    @1
    cA
    c1
    cA
    cmin
    co
    #
    caddc
    co
    #
    cB
    @7
    caddc
    co
    #
    cfz
    co
    #
    @5
    cen
    @0
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    @7
    cz
    wcel
    #
    @1
    @10
    cen
    wbr
    cA
    cB
    eluzel2
    #
    cA
    cB
    eluzelz
    #
    @0
    c1
    cz
    wcel
    @11
    @12
    1z
    @13
    c1
    cA
    zsubcl
    sylancr
    @7
    cA
    cB
    fzen
    syl3anc
    @0
    @8
    c1
    @9
    @4
    cfz
    @0
    cA
    cc
    wcel
    c1
    cc
    wcel
    #
    @8
    c1
    wceq
    @0
    cA
    @13
    zcnd
    #
    ax-1cn
    cA
    c1
    pncan3
    sylancl
    @0
    @9
    c1
    @3
    caddc
    co
    #
    @4
    @0
    cB
    c1
    cA
    @0
    cB
    @14
    zcnd
    #
    @0
    1cnd
    @16
    addsub12d
    @0
    @15
    @3
    cc
    wcel
    @17
    @4
    wceq
    ax-1cn
    @0
    cB
    cA
    @18
    @16
    subcld
    c1
    @3
    addcom
    sylancr
    eqtrd
    oveq12d
    breqtrd
    @1
    @5
    hasheni
    syl
    @0
    @3
    cn0
    wcel
    @4
    cn0
    wcel
    @6
    @4
    wceq
    cA
    cB
    uznn0sub
    @3
    peano2nn0
    @4
    hashfz1
    3syl
    eqtrd
end

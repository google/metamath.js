include "cz.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfzo.mm"
include "cmin.mm"
include "cpr.mm"
include "cun.mm"
include "wceq.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "cle.mm"
include "simp1.mm"
include "peano2zm.mm"
include "3ad2ant2.mm"
include "zltlem1.mm"
include "biimp3a.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "fzosplitpr.mm"
include "syl.mm"
include "wb.mm"
include "zcn.mm"
include "1cnd.mm"
include "2cnd.mm"
include "subadd23d.mm"
include "2m1e1.mm"
include "oveq2i.mm"
include "syl6req.mm"
include "oveq2d.mm"
include "cc.mm"
include "npcan1.mm"
include "eqcomd.mm"
include "preq2d.mm"
include "uneq2d.mm"
include "eqeq12d.mm"
include "mpbird.mm"

theorem fzosplitprm1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ZZ /\ B e. ZZ /\ A < B ) -> ( A ..^ ( B + 1 ) ) = ( ( A ..^ ( B - 1 ) ) u. { ( B - 1 ) , B } ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    cA
    cB
    clt
    wbr
    #
    w3a
    #
    cA
    cB
    c1
    caddc
    co
    #
    cfzo
    co
    #
    cA
    cB
    c1
    cmin
    co
    #
    cfzo
    co
    #
    @6
    cB
    cpr
    #
    cun
    #
    wceq
    #
    cA
    @6
    c2
    caddc
    co
    #
    cfzo
    co
    #
    @7
    @6
    @6
    c1
    caddc
    co
    #
    cpr
    #
    cun
    #
    wceq
    #
    @3
    @6
    cA
    cuz
    cfv
    wcel
    #
    @16
    @3
    @0
    @6
    cz
    wcel
    #
    cA
    @6
    cle
    wbr
    #
    @17
    @0
    @1
    @2
    simp1
    @1
    @0
    @18
    @2
    cB
    peano2zm
    3ad2ant2
    @0
    @1
    @2
    @19
    cA
    cB
    zltlem1
    biimp3a
    cA
    @6
    eluz2
    syl3anbrc
    cA
    @6
    fzosplitpr
    syl
    @1
    @0
    @10
    @16
    wb
    @2
    @1
    @5
    @12
    @9
    @15
    @1
    @4
    @11
    cA
    cfzo
    @1
    @11
    cB
    c2
    c1
    cmin
    co
    #
    caddc
    co
    @4
    @1
    cB
    c1
    c2
    cB
    zcn
    #
    @1
    1cnd
    @1
    2cnd
    subadd23d
    @20
    c1
    cB
    caddc
    2m1e1
    oveq2i
    syl6req
    oveq2d
    @1
    @8
    @14
    @7
    @1
    cB
    @13
    @6
    @1
    @13
    cB
    @1
    cB
    cc
    wcel
    @13
    cB
    wceq
    @21
    cB
    npcan1
    syl
    eqcomd
    preq2d
    uneq2d
    eqeq12d
    3ad2ant2
    mpbird
end

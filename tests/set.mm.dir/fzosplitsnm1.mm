include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cuz.mm"
include "cfv.mm"
include "wa.mm"
include "cfzo.mm"
include "cmin.mm"
include "cun.mm"
include "csn.mm"
include "cc.mm"
include "wceq.mm"
include "eluzelz.mm"
include "zcnd.mm"
include "adantl.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "eqcomd.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "cfz.mm"
include "eluzp1m1.mm"
include "peano2zm.mm"
include "uzid.mm"
include "peano2uz.mm"
include "4syl.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"
include "fzosplit.mm"
include "syl.mm"
include "fzosn.mm"
include "uneq2d.mm"
include "3eqtrd.mm"

theorem fzosplitsnm1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ZZ /\ B e. ( ZZ>= ` ( A + 1 ) ) ) -> ( A ..^ B ) = ( ( A ..^ ( B - 1 ) ) u. { ( B - 1 ) } ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cA
    c1
    caddc
    co
    #
    cuz
    cfv
    wcel
    #
    wa
    #
    cA
    cB
    cfzo
    co
    cA
    cB
    c1
    cmin
    co
    #
    c1
    caddc
    co
    #
    cfzo
    co
    #
    cA
    @4
    cfzo
    co
    #
    @4
    @5
    cfzo
    co
    #
    cun
    #
    @7
    @4
    csn
    #
    cun
    @3
    cB
    @5
    cA
    cfzo
    @3
    cB
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    cB
    @5
    wceq
    @2
    @11
    @0
    @2
    cB
    @1
    cB
    eluzelz
    #
    zcnd
    adantl
    ax-1cn
    @11
    @12
    wa
    @5
    cB
    cB
    c1
    npcan
    eqcomd
    sylancl
    oveq2d
    @3
    @4
    cA
    @5
    cfz
    co
    wcel
    #
    @6
    @9
    wceq
    @3
    @4
    cA
    cuz
    cfv
    wcel
    @5
    @4
    cuz
    cfv
    #
    wcel
    #
    @14
    cA
    cB
    eluzp1m1
    @3
    cB
    cz
    wcel
    #
    @4
    cz
    wcel
    #
    @4
    @15
    wcel
    @16
    @2
    @17
    @0
    @13
    adantl
    cB
    peano2zm
    #
    @4
    uzid
    @4
    @4
    peano2uz
    4syl
    @4
    cA
    @5
    elfzuzb
    sylanbrc
    cA
    @5
    @4
    fzosplit
    syl
    @3
    @8
    @10
    @7
    @3
    @18
    @8
    @10
    wceq
    @2
    @18
    @0
    @2
    @17
    @18
    @13
    @19
    syl
    adantl
    @4
    fzosn
    syl
    uneq2d
    3eqtrd
end

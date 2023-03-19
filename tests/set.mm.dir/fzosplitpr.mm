include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c2.mm"
include "caddc.mm"
include "co.mm"
include "cfzo.mm"
include "c1.mm"
include "csn.mm"
include "cun.mm"
include "cpr.mm"
include "wceq.mm"
include "df-2.mm"
include "a1i.mm"
include "oveq2d.mm"
include "cc.mm"
include "eluzelcn.mm"
include "1cnd.mm"
include "add32r.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "peano2uz.mm"
include "fzosplitsn.mm"
include "syl.mm"
include "uneq1d.mm"
include "unass.mm"
include "df-pr.mm"
include "eqcomi.mm"
include "uneq2d.mm"
include "3eqtrd.mm"

theorem fzosplitpr
  let cA: class A
  let cB: class B


  assert |- ( B e. ( ZZ>= ` A ) -> ( A ..^ ( B + 2 ) ) = ( ( A ..^ B ) u. { B , ( B + 1 ) } ) )

  proof
    cB
    cA
    cuz
    cfv
    #
    wcel
    #
    cA
    cB
    c2
    caddc
    co
    #
    cfzo
    co
    cA
    cB
    c1
    caddc
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
    @3
    cfzo
    co
    #
    @3
    csn
    #
    cun
    #
    cA
    cB
    cfzo
    co
    #
    cB
    @3
    cpr
    #
    cun
    #
    @1
    @2
    @4
    cA
    cfzo
    @1
    @2
    cB
    c1
    c1
    caddc
    co
    #
    caddc
    co
    #
    @4
    @1
    c2
    @12
    cB
    caddc
    c2
    @12
    wceq
    @1
    df-2
    a1i
    oveq2d
    @1
    cB
    cc
    wcel
    c1
    cc
    wcel
    #
    @14
    @13
    @4
    wceq
    cA
    cB
    eluzelcn
    @1
    1cnd
    #
    @15
    cB
    c1
    c1
    add32r
    syl3anc
    eqtrd
    oveq2d
    @1
    @3
    @0
    wcel
    @5
    @8
    wceq
    cA
    cB
    peano2uz
    cA
    @3
    fzosplitsn
    syl
    @1
    @8
    @9
    cB
    csn
    #
    cun
    #
    @7
    cun
    #
    @9
    @16
    @7
    cun
    #
    cun
    #
    @11
    @1
    @6
    @17
    @7
    cA
    cB
    fzosplitsn
    uneq1d
    @18
    @20
    wceq
    @1
    @9
    @16
    @7
    unass
    a1i
    @1
    @19
    @10
    @9
    @19
    @10
    wceq
    @1
    @10
    @19
    cB
    @3
    df-pr
    eqcomi
    a1i
    uneq2d
    3eqtrd
    3eqtrd
end

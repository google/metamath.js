include "cc0.mm"
include "caddc.mm"
include "co.mm"
include "cfzo.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "cz.mm"
include "cmin.mm"
include "simplr.mm"
include "wo.mm"
include "fzospliti.mm"
include "ad2ant2r.mm"
include "ord.mm"
include "mpd.mm"
include "simprl.mm"
include "fzosubel.mm"
include "syl2anc.mm"
include "wceq.mm"
include "zcn.mm"
include "subidd.mm"
include "syl.mm"
include "zcnd.mm"
include "simprr.mm"
include "pncan2d.mm"
include "oveq12d.mm"
include "eleqtrd.mm"

theorem fzocatel
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. ( 0 ..^ ( B + C ) ) /\ -. A e. ( 0 ..^ B ) ) /\ ( B e. ZZ /\ C e. ZZ ) ) -> ( A - B ) e. ( 0 ..^ C ) )

  proof
    cA
    cc0
    cB
    cC
    caddc
    co
    #
    cfzo
    co
    wcel
    #
    cA
    cc0
    cB
    cfzo
    co
    wcel
    #
    wn
    #
    wa
    #
    cB
    cz
    wcel
    #
    cC
    cz
    wcel
    #
    wa
    #
    wa
    #
    cA
    cB
    cmin
    co
    #
    cB
    cB
    cmin
    co
    #
    @0
    cB
    cmin
    co
    #
    cfzo
    co
    #
    cc0
    cC
    cfzo
    co
    @8
    cA
    cB
    @0
    cfzo
    co
    wcel
    #
    @5
    @9
    @12
    wcel
    @8
    @3
    @13
    @1
    @3
    @7
    simplr
    @8
    @2
    @13
    @1
    @5
    @2
    @13
    wo
    @3
    @6
    cA
    cc0
    @0
    cB
    fzospliti
    ad2ant2r
    ord
    mpd
    @4
    @5
    @6
    simprl
    #
    cA
    cB
    @0
    cB
    fzosubel
    syl2anc
    @8
    @10
    cc0
    @11
    cC
    cfzo
    @8
    @5
    @10
    cc0
    wceq
    @14
    @5
    cB
    cB
    zcn
    subidd
    syl
    @8
    cB
    cC
    @8
    cB
    @14
    zcnd
    @8
    cC
    @4
    @5
    @6
    simprr
    zcnd
    pncan2d
    oveq12d
    eleqtrd
end

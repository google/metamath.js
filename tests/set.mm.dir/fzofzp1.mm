include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "cfz.mm"
include "cz.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "elfzoel1.mm"
include "uzid.mm"
include "peano2uz.mm"
include "fzoss1.mm"
include "4syl.mm"
include "1z.mm"
include "fzoaddel.mm"
include "mpan2.mm"
include "sseldd.mm"
include "wceq.mm"
include "elfzoel2.mm"
include "fzval3.mm"
include "syl.mm"
include "eleqtrrd.mm"

theorem fzofzp1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( C e. ( A ..^ B ) -> ( C + 1 ) e. ( A ... B ) )

  proof
    cC
    cA
    cB
    cfzo
    co
    wcel
    #
    cC
    c1
    caddc
    co
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
    cfz
    co
    #
    @0
    cA
    c1
    caddc
    co
    #
    @2
    cfzo
    co
    #
    @3
    @1
    @0
    cA
    cz
    wcel
    cA
    cA
    cuz
    cfv
    #
    wcel
    @5
    @7
    wcel
    @6
    @3
    wss
    cC
    cA
    cB
    elfzoel1
    cA
    uzid
    cA
    cA
    peano2uz
    @5
    cA
    @2
    fzoss1
    4syl
    @0
    c1
    cz
    wcel
    @1
    @6
    wcel
    1z
    cC
    cA
    cB
    c1
    fzoaddel
    mpan2
    sseldd
    @0
    cB
    cz
    wcel
    @4
    @3
    wceq
    cC
    cA
    cB
    elfzoel2
    cA
    cB
    fzval3
    syl
    eleqtrrd
end

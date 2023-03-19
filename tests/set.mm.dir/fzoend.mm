include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "cuz.mm"
include "cfv.mm"
include "id.mm"
include "cz.mm"
include "wceq.mm"
include "elfzoel2.mm"
include "fzoval.mm"
include "syl.mm"
include "eleqtrd.mm"
include "elfzuz3.mm"
include "eluzfz2.mm"
include "eleqtrrd.mm"

theorem fzoend
  let cA: class A
  let cB: class B


  assert |- ( A e. ( A ..^ B ) -> ( B - 1 ) e. ( A ..^ B ) )

  proof
    cA
    cA
    cB
    cfzo
    co
    #
    wcel
    #
    cB
    c1
    cmin
    co
    #
    cA
    @2
    cfz
    co
    #
    @0
    @1
    @2
    cA
    cuz
    cfv
    wcel
    #
    @2
    @3
    wcel
    @1
    cA
    @3
    wcel
    @4
    @1
    cA
    @0
    @3
    @1
    id
    @1
    cB
    cz
    wcel
    @0
    @3
    wceq
    cA
    cA
    cB
    elfzoel2
    cA
    cB
    fzoval
    syl
    #
    eleqtrd
    cA
    cA
    @2
    elfzuz3
    syl
    cA
    @2
    eluzfz2
    syl
    @5
    eleqtrrd
end

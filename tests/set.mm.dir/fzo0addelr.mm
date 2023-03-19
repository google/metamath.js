include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "caddc.mm"
include "fzo0addel.mm"
include "cc.mm"
include "wceq.mm"
include "zcn.mm"
include "elfzoel2.mm"
include "zcnd.mm"
include "addcom.mm"
include "syl2anr.mm"
include "oveq2d.mm"
include "eleqtrrd.mm"

theorem fzo0addelr
  let cA: class A
  let cC: class C
  let cD: class D


  assert |- ( ( A e. ( 0 ..^ C ) /\ D e. ZZ ) -> ( A + D ) e. ( D ..^ ( D + C ) ) )

  proof
    cA
    cc0
    cC
    cfzo
    co
    wcel
    #
    cD
    cz
    wcel
    #
    wa
    #
    cA
    cD
    caddc
    co
    cD
    cC
    cD
    caddc
    co
    #
    cfzo
    co
    cD
    cD
    cC
    caddc
    co
    #
    cfzo
    co
    cA
    cC
    cD
    fzo0addel
    @2
    @4
    @3
    cD
    cfzo
    @1
    cD
    cc
    wcel
    cC
    cc
    wcel
    @4
    @3
    wceq
    @0
    cD
    zcn
    @0
    cC
    cA
    cc0
    cC
    elfzoel2
    zcnd
    cD
    cC
    addcom
    syl2anr
    oveq2d
    eleqtrrd
end

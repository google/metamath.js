include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "caddc.mm"
include "fzoaddel.mm"
include "wceq.mm"
include "cc.mm"
include "zcn.mm"
include "addid2.mm"
include "eqcomd.mm"
include "syl.mm"
include "adantl.mm"
include "oveq1d.mm"
include "eleqtrrd.mm"

theorem fzo0addel
  let cA: class A
  let cC: class C
  let cD: class D


  assert |- ( ( A e. ( 0 ..^ C ) /\ D e. ZZ ) -> ( A + D ) e. ( D ..^ ( C + D ) ) )

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
    cc0
    cD
    caddc
    co
    #
    cC
    cD
    caddc
    co
    #
    cfzo
    co
    cD
    @4
    cfzo
    co
    cA
    cc0
    cC
    cD
    fzoaddel
    @2
    cD
    @3
    @4
    cfzo
    @1
    cD
    @3
    wceq
    #
    @0
    @1
    cD
    cc
    wcel
    #
    @5
    cD
    zcn
    @6
    @3
    cD
    cD
    addid2
    eqcomd
    syl
    adantl
    oveq1d
    eleqtrrd
end

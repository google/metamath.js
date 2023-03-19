include "caddc.mm"
include "co.mm"
include "cfzo.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "wa.mm"
include "cmin.mm"
include "fzosubel.mm"
include "3ad2antr1.mm"
include "wceq.mm"
include "cc.mm"
include "zcn.mm"
include "pncan2.mm"
include "3adant3.mm"
include "3adant2.mm"
include "oveq12d.mm"
include "syl3an.mm"
include "adantl.mm"
include "eleqtrd.mm"

theorem fzosubel2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A e. ( ( B + C ) ..^ ( B + D ) ) /\ ( B e. ZZ /\ C e. ZZ /\ D e. ZZ ) ) -> ( A - B ) e. ( C ..^ D ) )

  proof
    cA
    cB
    cC
    caddc
    co
    #
    cB
    cD
    caddc
    co
    #
    cfzo
    co
    wcel
    #
    cB
    cz
    wcel
    #
    cC
    cz
    wcel
    #
    cD
    cz
    wcel
    #
    w3a
    #
    wa
    cA
    cB
    cmin
    co
    #
    @0
    cB
    cmin
    co
    #
    @1
    cB
    cmin
    co
    #
    cfzo
    co
    #
    cC
    cD
    cfzo
    co
    #
    @2
    @4
    @3
    @7
    @10
    wcel
    @5
    cA
    @0
    @1
    cB
    fzosubel
    3ad2antr1
    @6
    @10
    @11
    wceq
    #
    @2
    @3
    cB
    cc
    wcel
    #
    @4
    cC
    cc
    wcel
    #
    @5
    cD
    cc
    wcel
    #
    @12
    cB
    zcn
    cC
    zcn
    cD
    zcn
    @13
    @14
    @15
    w3a
    @8
    cC
    @9
    cD
    cfzo
    @13
    @14
    @8
    cC
    wceq
    @15
    cB
    cC
    pncan2
    3adant3
    @13
    @15
    @9
    cD
    wceq
    @14
    cB
    cD
    pncan2
    3adant2
    oveq12d
    syl3an
    adantl
    eleqtrd
end

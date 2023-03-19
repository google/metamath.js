include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cfzo.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "caddc.mm"
include "fzoaddel.mm"
include "3adant2.mm"
include "wceq.mm"
include "cc.mm"
include "zcn.mm"
include "wa.mm"
include "addid2.mm"
include "adantl.mm"
include "npcan.mm"
include "oveq12d.mm"
include "syl2an.mm"
include "3adant1.mm"
include "eleqtrd.mm"

theorem fzoaddel2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. ( 0 ..^ ( B - C ) ) /\ B e. ZZ /\ C e. ZZ ) -> ( A + C ) e. ( C ..^ B ) )

  proof
    cA
    cc0
    cB
    cC
    cmin
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
    w3a
    cA
    cC
    caddc
    co
    #
    cc0
    cC
    caddc
    co
    #
    @0
    cC
    caddc
    co
    #
    cfzo
    co
    #
    cC
    cB
    cfzo
    co
    #
    @1
    @3
    @4
    @7
    wcel
    @2
    cA
    cc0
    @0
    cC
    fzoaddel
    3adant2
    @2
    @3
    @7
    @8
    wceq
    #
    @1
    @2
    cB
    cc
    wcel
    #
    cC
    cc
    wcel
    #
    @9
    @3
    cB
    zcn
    cC
    zcn
    @10
    @11
    wa
    @5
    cC
    @6
    cB
    cfzo
    @11
    @5
    cC
    wceq
    @10
    cC
    addid2
    adantl
    cB
    cC
    npcan
    oveq12d
    syl2an
    3adant1
    eleqtrd
end

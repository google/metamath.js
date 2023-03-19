include "cc.mm"
include "wcel.mm"
include "cre.mm"
include "cfv.mm"
include "cc0.mm"
include "cpi.mm"
include "cioo.mm"
include "co.mm"
include "w3a.mm"
include "cacos.mm"
include "wceq.mm"
include "ccos.mm"
include "cosacos.mm"
include "3ad2ant1.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "syl5ibcom.mm"
include "acoscos.mm"
include "3adant1.mm"
include "impbid.mm"

theorem acoscosb
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC /\ ( Re ` B ) e. ( 0 (,) _pi ) ) -> ( ( arccos ` A ) = B <-> ( cos ` B ) = A ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cB
    cre
    cfv
    cc0
    cpi
    cioo
    co
    wcel
    #
    w3a
    #
    cA
    cacos
    cfv
    #
    cB
    wceq
    #
    cB
    ccos
    cfv
    #
    cA
    wceq
    #
    @3
    @4
    ccos
    cfv
    #
    cA
    wceq
    #
    @5
    @7
    @0
    @1
    @9
    @2
    cA
    cosacos
    3ad2ant1
    @5
    @8
    @6
    cA
    @4
    cB
    ccos
    fveq2
    eqeq1d
    syl5ibcom
    @3
    @6
    cacos
    cfv
    #
    cB
    wceq
    #
    @7
    @5
    @1
    @2
    @11
    @0
    cB
    acoscos
    3adant1
    @7
    @10
    @4
    cB
    @6
    cA
    cacos
    fveq2
    eqeq1d
    syl5ibcom
    impbid
end

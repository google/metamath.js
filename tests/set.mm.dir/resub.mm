include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cre.mm"
include "cfv.mm"
include "cmin.mm"
include "wceq.mm"
include "negcl.mm"
include "readd.mm"
include "sylan2.mm"
include "reneg.mm"
include "adantl.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "negsub.mm"
include "fveq2d.mm"
include "recl.mm"
include "recnd.mm"
include "syl2an.mm"
include "3eqtr3d.mm"

theorem resub
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( Re ` ( A - B ) ) = ( ( Re ` A ) - ( Re ` B ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    cB
    cneg
    #
    caddc
    co
    #
    cre
    cfv
    #
    cA
    cre
    cfv
    #
    cB
    cre
    cfv
    #
    cneg
    #
    caddc
    co
    #
    cA
    cB
    cmin
    co
    #
    cre
    cfv
    @6
    @7
    cmin
    co
    #
    @2
    @5
    @6
    @3
    cre
    cfv
    #
    caddc
    co
    #
    @9
    @1
    @0
    @3
    cc
    wcel
    @5
    @13
    wceq
    cB
    negcl
    cA
    @3
    readd
    sylan2
    @2
    @12
    @8
    @6
    caddc
    @1
    @12
    @8
    wceq
    @0
    cB
    reneg
    adantl
    oveq2d
    eqtrd
    @2
    @4
    @10
    cre
    cA
    cB
    negsub
    fveq2d
    @0
    @6
    cc
    wcel
    @7
    cc
    wcel
    @9
    @11
    wceq
    @1
    @0
    @6
    cA
    recl
    recnd
    @1
    @7
    cB
    recl
    recnd
    @6
    @7
    negsub
    syl2an
    3eqtr3d
end

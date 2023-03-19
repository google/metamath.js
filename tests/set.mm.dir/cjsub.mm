include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "ccj.mm"
include "cfv.mm"
include "cmin.mm"
include "wceq.mm"
include "negcl.mm"
include "cjadd.mm"
include "sylan2.mm"
include "negsub.mm"
include "fveq2d.mm"
include "cjneg.mm"
include "adantl.mm"
include "oveq2d.mm"
include "cjcl.mm"
include "syl2an.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"

theorem cjsub
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( * ` ( A - B ) ) = ( ( * ` A ) - ( * ` B ) ) )

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
    ccj
    cfv
    #
    cA
    ccj
    cfv
    #
    @3
    ccj
    cfv
    #
    caddc
    co
    #
    cA
    cB
    cmin
    co
    #
    ccj
    cfv
    @6
    cB
    ccj
    cfv
    #
    cmin
    co
    #
    @1
    @0
    @3
    cc
    wcel
    @5
    @8
    wceq
    cB
    negcl
    cA
    @3
    cjadd
    sylan2
    @2
    @4
    @9
    ccj
    cA
    cB
    negsub
    fveq2d
    @2
    @8
    @6
    @10
    cneg
    #
    caddc
    co
    #
    @11
    @2
    @7
    @12
    @6
    caddc
    @1
    @7
    @12
    wceq
    @0
    cB
    cjneg
    adantl
    oveq2d
    @0
    @6
    cc
    wcel
    @10
    cc
    wcel
    @13
    @11
    wceq
    @1
    cA
    cjcl
    cB
    cjcl
    @6
    @10
    negsub
    syl2an
    eqtrd
    3eqtr3d
end

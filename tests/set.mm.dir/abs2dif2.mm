include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "cmin.mm"
include "cle.mm"
include "wbr.mm"
include "negcl.mm"
include "abstri.mm"
include "sylan2.mm"
include "negsub.mm"
include "fveq2d.mm"
include "wceq.mm"
include "absneg.mm"
include "adantl.mm"
include "oveq2d.mm"
include "3brtr3d.mm"

theorem abs2dif2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( abs ` ( A - B ) ) <_ ( ( abs ` A ) + ( abs ` B ) ) )

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
    cabs
    cfv
    #
    cA
    cabs
    cfv
    #
    @3
    cabs
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
    cabs
    cfv
    @6
    cB
    cabs
    cfv
    #
    caddc
    co
    cle
    @1
    @0
    @3
    cc
    wcel
    @5
    @8
    cle
    wbr
    cB
    negcl
    cA
    @3
    abstri
    sylan2
    @2
    @4
    @9
    cabs
    cA
    cB
    negsub
    fveq2d
    @2
    @7
    @10
    @6
    caddc
    @1
    @7
    @10
    wceq
    @0
    cB
    absneg
    adantl
    oveq2d
    3brtr3d
end

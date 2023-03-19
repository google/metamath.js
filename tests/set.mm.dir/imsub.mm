include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cim.mm"
include "cfv.mm"
include "cmin.mm"
include "wceq.mm"
include "negcl.mm"
include "imadd.mm"
include "sylan2.mm"
include "imneg.mm"
include "adantl.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "negsub.mm"
include "fveq2d.mm"
include "imcl.mm"
include "recnd.mm"
include "syl2an.mm"
include "3eqtr3d.mm"

theorem imsub
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( Im ` ( A - B ) ) = ( ( Im ` A ) - ( Im ` B ) ) )

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
    cim
    cfv
    #
    cA
    cim
    cfv
    #
    cB
    cim
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
    cim
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
    cim
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
    imadd
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
    imneg
    adantl
    oveq2d
    eqtrd
    @2
    @4
    @10
    cim
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
    imcl
    recnd
    @1
    @7
    cB
    imcl
    recnd
    @6
    @7
    negsub
    syl2an
    3eqtr3d
end

include "cfn.mm"
include "wcel.mm"
include "cxp.mm"
include "chash.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "c0.mm"
include "cif.mm"
include "xpeq2.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "0fin.mm"
include "elimel.mm"
include "hashxplem.mm"
include "dedth.mm"
include "impcom.mm"

theorem hashxp
  let cA: class A
  let cB: class B


  assert |- ( ( A e. Fin /\ B e. Fin ) -> ( # ` ( A X. B ) ) = ( ( # ` A ) x. ( # ` B ) ) )

  proof
    cB
    cfn
    wcel
    #
    cA
    cfn
    wcel
    #
    cA
    cB
    cxp
    #
    chash
    cfv
    #
    cA
    chash
    cfv
    #
    cB
    chash
    cfv
    #
    cmul
    co
    #
    wceq
    #
    @0
    @1
    @7
    wi
    @1
    cA
    @0
    cB
    c0
    cif
    #
    cxp
    #
    chash
    cfv
    #
    @4
    @8
    chash
    cfv
    #
    cmul
    co
    #
    wceq
    #
    wi
    cB
    c0
    cB
    @8
    wceq
    #
    @7
    @13
    @1
    @14
    @3
    @10
    @6
    @12
    @14
    @2
    @9
    chash
    cB
    @8
    cA
    xpeq2
    fveq2d
    @14
    @5
    @11
    @4
    cmul
    cB
    @8
    chash
    fveq2
    oveq2d
    eqeq12d
    imbi2d
    cA
    @8
    cB
    c0
    cfn
    0fin
    elimel
    hashxplem
    dedth
    impcom
end

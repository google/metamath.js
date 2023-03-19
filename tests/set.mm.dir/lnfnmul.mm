include "clf.mm"
include "wcel.mm"
include "cc.mm"
include "chil.mm"
include "csm.mm"
include "co.mm"
include "cfv.mm"
include "cmul.mm"
include "wceq.mm"
include "wa.mm"
include "wi.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "cif.mm"
include "fveq1.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "0lnfn.mm"
include "elimel.mm"
include "lnfnmuli.mm"
include "dedth.mm"
include "3impib.mm"

theorem lnfnmul
  let cA: class A
  let cB: class B
  let cT: class T


  assert |- ( ( T e. LinFn /\ A e. CC /\ B e. ~H ) -> ( T ` ( A .h B ) ) = ( A x. ( T ` B ) ) )

  proof
    cT
    clf
    wcel
    #
    cA
    cc
    wcel
    #
    cB
    chil
    wcel
    #
    cA
    cB
    csm
    co
    #
    cT
    cfv
    #
    cA
    cB
    cT
    cfv
    #
    cmul
    co
    #
    wceq
    #
    @0
    @1
    @2
    wa
    #
    @7
    wi
    @8
    @3
    @0
    cT
    chil
    cc0
    csn
    cxp
    #
    cif
    #
    cfv
    #
    cA
    cB
    @10
    cfv
    #
    cmul
    co
    #
    wceq
    #
    wi
    cT
    @9
    cT
    @10
    wceq
    #
    @7
    @14
    @8
    @15
    @4
    @11
    @6
    @13
    @3
    cT
    @10
    fveq1
    @15
    @5
    @12
    cA
    cmul
    cB
    cT
    @10
    fveq1
    oveq2d
    eqeq12d
    imbi2d
    cA
    cB
    @10
    cT
    @9
    clf
    0lnfn
    elimel
    lnfnmuli
    dedth
    3impib
end

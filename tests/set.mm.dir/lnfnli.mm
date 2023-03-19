include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "csm.mm"
include "co.mm"
include "cva.mm"
include "cfv.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "clf.mm"
include "wa.mm"
include "lnfnl.mm"
include "mpanl1.mm"
include "3impb.mm"

theorem lnfnli
  let cA: class A
  let cB: class B
  let cC: class C
  let cT: class T
  assume lnfnl.1: |- T e. LinFn


  assert |- ( ( A e. CC /\ B e. ~H /\ C e. ~H ) -> ( T ` ( ( A .h B ) +h C ) ) = ( ( A x. ( T ` B ) ) + ( T ` C ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    chil
    wcel
    #
    cC
    chil
    wcel
    #
    cA
    cB
    csm
    co
    cC
    cva
    co
    cT
    cfv
    cA
    cB
    cT
    cfv
    cmul
    co
    cC
    cT
    cfv
    caddc
    co
    wceq
    #
    cT
    clf
    wcel
    @0
    @1
    @2
    wa
    @3
    lnfnl.1
    cA
    cB
    cC
    cT
    lnfnl
    mpanl1
    3impb
end

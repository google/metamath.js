include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "csm.mm"
include "co.mm"
include "cva.mm"
include "cfv.mm"
include "wceq.mm"
include "clo.mm"
include "wa.mm"
include "lnopl.mm"
include "mpanl1.mm"
include "3impb.mm"

theorem lnopli
  let cA: class A
  let cB: class B
  let cC: class C
  let cT: class T
  assume lnopl.1: |- T e. LinOp


  assert |- ( ( A e. CC /\ B e. ~H /\ C e. ~H ) -> ( T ` ( ( A .h B ) +h C ) ) = ( ( A .h ( T ` B ) ) +h ( T ` C ) ) )

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
    csm
    co
    cC
    cT
    cfv
    cva
    co
    wceq
    #
    cT
    clo
    wcel
    @0
    @1
    @2
    wa
    @3
    lnopl.1
    cA
    cB
    cC
    cT
    lnopl
    mpanl1
    3impb
end

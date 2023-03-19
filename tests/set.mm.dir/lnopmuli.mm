include "clo.mm"
include "wcel.mm"
include "cc.mm"
include "chil.mm"
include "csm.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "lnopmul.mm"
include "mp3an1.mm"

theorem lnopmuli
  let cA: class A
  let cB: class B
  let cT: class T
  assume lnopl.1: |- T e. LinOp


  assert |- ( ( A e. CC /\ B e. ~H ) -> ( T ` ( A .h B ) ) = ( A .h ( T ` B ) ) )

  proof
    cT
    clo
    wcel
    cA
    cc
    wcel
    cB
    chil
    wcel
    cA
    cB
    csm
    co
    cT
    cfv
    cA
    cB
    cT
    cfv
    csm
    co
    wceq
    lnopl.1
    cA
    cB
    cT
    lnopmul
    mp3an1
end

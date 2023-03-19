include "wss.mm"
include "cmpt.mm"
include "cres.mm"
include "wceq.mm"
include "resmpt.mm"
include "ax-mp.mm"

theorem resmpti
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume resmpti.1: |- B C_ A

  disjoint A x
  disjoint B x
  assert |- ( ( x e. A |-> C ) |` B ) = ( x e. B |-> C )

  proof
    cB
    cA
    wss
    vx
    cA
    cC
    cmpt
    cB
    cres
    vx
    cB
    cC
    cmpt
    wceq
    resmpti.1
    vx
    cA
    cB
    cC
    resmpt
    ax-mp
end

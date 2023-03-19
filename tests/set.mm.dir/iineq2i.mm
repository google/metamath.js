include "wceq.mm"
include "ciin.mm"
include "iineq2.mm"
include "mprg.mm"

theorem iineq2i
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume iuneq2i.1: |- ( x e. A -> B = C )


  assert |- |^|_ x e. A B = |^|_ x e. A C

  proof
    cB
    cC
    wceq
    vx
    cA
    cB
    ciin
    vx
    cA
    cC
    ciin
    wceq
    vx
    cA
    vx
    cA
    cB
    cC
    iineq2
    iuneq2i.1
    mprg
end

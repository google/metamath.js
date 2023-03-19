include "wceq.mm"
include "ciun.mm"
include "iuneq2.mm"
include "mprg.mm"

theorem iuneq2i
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume iuneq2i.1: |- ( x e. A -> B = C )


  assert |- U_ x e. A B = U_ x e. A C

  proof
    cB
    cC
    wceq
    vx
    cA
    cB
    ciun
    vx
    cA
    cC
    ciun
    wceq
    vx
    cA
    vx
    cA
    cB
    cC
    iuneq2
    iuneq2i.1
    mprg
end

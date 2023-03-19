include "wceq.mm"
include "nfeq.mm"
include "id.mm"
include "eqidd.mm"
include "iuneq12df.mm"

theorem iuneq2f
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume iuneq2f.1: |- F/_ x A
  assume iuneq2f.2: |- F/_ x B


  assert |- ( A = B -> U_ x e. A C = U_ x e. B C )

  proof
    cA
    cB
    wceq
    #
    vx
    cA
    cB
    cC
    cC
    vx
    cA
    cB
    iuneq2f.1
    iuneq2f.2
    nfeq
    iuneq2f.1
    iuneq2f.2
    @0
    id
    @0
    cC
    eqidd
    iuneq12df
end

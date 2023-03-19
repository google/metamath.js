include "ciun.mm"
include "wss.mm"
include "wral.mm"
include "rgenw.mm"
include "iunss.mm"
include "mpbir.mm"

theorem bnj226
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume bnj226.1: |- B C_ C

  disjoint C x
  assert |- U_ x e. A B C_ C

  proof
    vx
    cA
    cB
    ciun
    cC
    wss
    cB
    cC
    wss
    #
    vx
    cA
    wral
    @0
    vx
    cA
    bnj226.1
    rgenw
    vx
    cA
    cB
    cC
    iunss
    mpbir
end

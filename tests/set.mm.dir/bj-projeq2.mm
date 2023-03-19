include "wceq.mm"
include "bj-cproj.mm"
include "wi.mm"
include "eqid.mm"
include "bj-projeq.mm"
include "ax-mp.mm"

theorem bj-projeq2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( B = C -> ( A Proj B ) = ( A Proj C ) )

  proof
    cA
    cA
    wceq
    cB
    cC
    wceq
    cA
    cB
    bj-cproj
    cA
    cC
    bj-cproj
    wceq
    wi
    cA
    eqid
    cA
    cB
    cA
    cC
    bj-projeq
    ax-mp
end

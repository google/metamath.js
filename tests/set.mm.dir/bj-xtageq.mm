include "wceq.mm"
include "bj-ctag.mm"
include "bj-tageq.mm"
include "xpeq2d.mm"

theorem bj-xtageq
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> ( C X. tag A ) = ( C X. tag B ) )

  proof
    cA
    cB
    wceq
    cA
    bj-ctag
    cB
    bj-ctag
    cC
    cA
    cB
    bj-tageq
    xpeq2d
end

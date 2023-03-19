include "bj-csngl.mm"
include "bj-ctag.mm"
include "bj-snglsstag.mm"
include "sseli.mm"

theorem bj-sngltagi
  let cA: class A
  let cB: class B


  assert |- ( A e. sngl B -> A e. tag B )

  proof
    cB
    bj-csngl
    cB
    bj-ctag
    cA
    cB
    bj-snglsstag
    sseli
end

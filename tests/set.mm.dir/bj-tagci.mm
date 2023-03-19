include "wcel.mm"
include "csn.mm"
include "bj-csngl.mm"
include "bj-ctag.mm"
include "bj-snglc.mm"
include "bj-sngltagi.mm"
include "sylbi.mm"

theorem bj-tagci
  let cA: class A
  let cB: class B


  assert |- ( A e. B -> { A } e. tag B )

  proof
    cA
    cB
    wcel
    cA
    csn
    #
    cB
    bj-csngl
    wcel
    @0
    cB
    bj-ctag
    wcel
    cA
    cB
    bj-snglc
    @0
    cB
    bj-sngltagi
    sylbi
end

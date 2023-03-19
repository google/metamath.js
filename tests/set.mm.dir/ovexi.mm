include "co.mm"
include "cvv.mm"
include "ovex.mm"
include "eqeltri.mm"

theorem ovexi
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume ovexi.1: |- A = ( B F C )


  assert |- A e. _V

  proof
    cA
    cB
    cC
    cF
    co
    cvv
    ovexi.1
    cB
    cC
    cF
    ovex
    eqeltri
end

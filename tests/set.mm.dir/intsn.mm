include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "cint.mm"
include "wceq.mm"
include "intsng.mm"
include "ax-mp.mm"

theorem intsn
  let cA: class A
  assume intsn.1: |- A e. _V


  assert |- |^| { A } = A

  proof
    cA
    cvv
    wcel
    cA
    csn
    cint
    cA
    wceq
    intsn.1
    cA
    cvv
    intsng
    ax-mp
end

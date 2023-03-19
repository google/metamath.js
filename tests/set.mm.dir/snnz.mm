include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "c0.mm"
include "wne.mm"
include "snnzg.mm"
include "ax-mp.mm"

theorem snnz
  let cA: class A
  assume snnz.1: |- A e. _V


  assert |- { A } =/= (/)

  proof
    cA
    cvv
    wcel
    cA
    csn
    c0
    wne
    snnz.1
    cA
    cvv
    snnzg
    ax-mp
end

include "csn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wcel.mm"
include "wn.mm"
include "elirr.mm"
include "disjsn.mm"
include "mpbir.mm"

theorem bj-disjcsn
  let cA: class A


  assert |- ( A i^i { A } ) = (/)

  proof
    cA
    cA
    csn
    cin
    c0
    wceq
    cA
    cA
    wcel
    wn
    cA
    elirr
    cA
    cA
    disjsn
    mpbir
end

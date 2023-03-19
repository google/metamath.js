include "word.mm"
include "wcel.mm"
include "wn.mm"
include "csn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "ordirr.mm"
include "disjsn.mm"
include "sylibr.mm"

theorem orddisj
  let cA: class A


  assert |- ( Ord A -> ( A i^i { A } ) = (/) )

  proof
    cA
    word
    cA
    cA
    wcel
    wn
    cA
    cA
    csn
    cin
    c0
    wceq
    cA
    ordirr
    cA
    cA
    disjsn
    sylibr
end

include "wne.mm"
include "csn.mm"
include "wcel.mm"
include "wn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "elsni.mm"
include "eqcomd.mm"
include "necon3ai.mm"
include "disjsn.mm"
include "sylibr.mm"

theorem disjsn2
  let cA: class A
  let cB: class B


  assert |- ( A =/= B -> ( { A } i^i { B } ) = (/) )

  proof
    cA
    cB
    wne
    cB
    cA
    csn
    #
    wcel
    #
    wn
    @0
    cB
    csn
    cin
    c0
    wceq
    @1
    cA
    cB
    @1
    cB
    cA
    cB
    cA
    elsni
    eqcomd
    necon3ai
    @0
    cB
    disjsn
    sylibr
end

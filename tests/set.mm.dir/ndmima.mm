include "csn.mm"
include "cima.mm"
include "c0.mm"
include "wceq.mm"
include "cdm.mm"
include "cin.mm"
include "wcel.mm"
include "wn.mm"
include "imadisj.mm"
include "disjsn.mm"
include "sylbbr.mm"

theorem ndmima
  let cA: class A
  let cB: class B


  assert |- ( -. A e. dom B -> ( B " { A } ) = (/) )

  proof
    cB
    cA
    csn
    #
    cima
    c0
    wceq
    cB
    cdm
    #
    @0
    cin
    c0
    wceq
    cA
    @1
    wcel
    wn
    cB
    @0
    imadisj
    @1
    cA
    disjsn
    sylbbr
end

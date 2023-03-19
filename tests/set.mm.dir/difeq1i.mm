include "wceq.mm"
include "cdif.mm"
include "difeq1.mm"
include "ax-mp.mm"

theorem difeq1i
  let cA: class A
  let cB: class B
  let cC: class C
  assume difeq1i.1: |- A = B


  assert |- ( A \ C ) = ( B \ C )

  proof
    cA
    cB
    wceq
    cA
    cC
    cdif
    cB
    cC
    cdif
    wceq
    difeq1i.1
    cA
    cB
    cC
    difeq1
    ax-mp
end

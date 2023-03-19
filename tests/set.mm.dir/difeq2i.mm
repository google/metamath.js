include "wceq.mm"
include "cdif.mm"
include "difeq2.mm"
include "ax-mp.mm"

theorem difeq2i
  let cA: class A
  let cB: class B
  let cC: class C
  assume difeq1i.1: |- A = B


  assert |- ( C \ A ) = ( C \ B )

  proof
    cA
    cB
    wceq
    cC
    cA
    cdif
    cC
    cB
    cdif
    wceq
    difeq1i.1
    cA
    cB
    cC
    difeq2
    ax-mp
end

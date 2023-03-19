include "wceq.mm"
include "cinf.mm"
include "infeq1.mm"
include "ax-mp.mm"

theorem infeq1i
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume infeq1i.1: |- B = C


  assert |- inf ( B , A , R ) = inf ( C , A , R )

  proof
    cB
    cC
    wceq
    cB
    cA
    cR
    cinf
    cC
    cA
    cR
    cinf
    wceq
    infeq1i.1
    cA
    cB
    cC
    cR
    infeq1
    ax-mp
end

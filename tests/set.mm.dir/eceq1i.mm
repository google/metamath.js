include "wceq.mm"
include "cec.mm"
include "eceq1.mm"
include "ax-mp.mm"

theorem eceq1i
  let cA: class A
  let cB: class B
  let cC: class C
  assume eceq1i.1: |- A = B


  assert |- [ A ] C = [ B ] C

  proof
    cA
    cB
    wceq
    cA
    cC
    cec
    cB
    cC
    cec
    wceq
    eceq1i.1
    cA
    cB
    cC
    eceq1
    ax-mp
end

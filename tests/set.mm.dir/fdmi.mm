include "wf.mm"
include "cdm.mm"
include "wceq.mm"
include "fdm.mm"
include "ax-mp.mm"

theorem fdmi
  let cA: class A
  let cB: class B
  let cF: class F
  assume fdmi.1: |- F : A --> B


  assert |- dom F = A

  proof
    cA
    cB
    cF
    wf
    cF
    cdm
    cA
    wceq
    fdmi.1
    cA
    cB
    cF
    fdm
    ax-mp
end

include "wfn.mm"
include "cdm.mm"
include "wceq.mm"
include "fnmpti.mm"
include "fndm.mm"
include "ax-mp.mm"

theorem dmmpti
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  assume fnmpti.1: |- B e. _V
  assume fnmpti.2: |- F = ( x e. A |-> B )

  disjoint A x
  assert |- dom F = A

  proof
    cF
    cA
    wfn
    cF
    cdm
    cA
    wceq
    vx
    cA
    cB
    cF
    fnmpti.1
    fnmpti.2
    fnmpti
    cA
    cF
    fndm
    ax-mp
end

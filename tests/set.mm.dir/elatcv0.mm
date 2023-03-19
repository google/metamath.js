include "cat.mm"
include "wcel.mm"
include "cch.mm"
include "c0h.mm"
include "ccv.mm"
include "wbr.mm"
include "ela.mm"
include "baib.mm"

theorem elatcv0
  let cA: class A
  let vx: setvar x
  let cB: class B


  assert |- ( A e. CH -> ( A e. HAtoms <-> 0H <oH A ) )

  proof
    cA
    cat
    wcel
    cA
    cch
    wcel
    c0h
    cA
    ccv
    wbr
    cA
    ela
    baib
end

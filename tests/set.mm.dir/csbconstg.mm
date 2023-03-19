include "nfcv.mm"
include "csbconstgf.mm"

theorem csbconstg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V

  disjoint B x
  assert |- ( A e. V -> [_ A / x ]_ B = B )

  proof
    vx
    cA
    cB
    cV
    vx
    cB
    nfcv
    csbconstgf
end

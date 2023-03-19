include "wcel.mm"
include "wnfc.mm"
include "csb.mm"
include "wceq.mm"
include "csbtt.mm"
include "mpan2.mm"

theorem csbconstgf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  assume csbconstgf.1: |- F/_ x B


  assert |- ( A e. V -> [_ A / x ]_ B = B )

  proof
    cA
    cV
    wcel
    vx
    cB
    wnfc
    vx
    cA
    cB
    csb
    cB
    wceq
    csbconstgf.1
    vx
    cA
    cB
    cV
    csbtt
    mpan2
end

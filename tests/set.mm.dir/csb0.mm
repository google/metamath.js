include "cvv.mm"
include "wcel.mm"
include "c0.mm"
include "csb.mm"
include "wceq.mm"
include "csbconstg.mm"
include "csbprc.mm"
include "pm2.61i.mm"

theorem csb0
  let vx: setvar x
  let cA: class A


  assert |- [_ A / x ]_ (/) = (/)

  proof
    cA
    cvv
    wcel
    vx
    cA
    c0
    csb
    c0
    wceq
    vx
    cA
    c0
    cvv
    csbconstg
    vx
    cA
    c0
    csbprc
    pm2.61i
end

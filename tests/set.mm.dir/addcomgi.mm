include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "addcom.mm"
include "cxp.mm"
include "ax-addf.mm"
include "fdmi.mm"
include "ndmovcom.mm"
include "pm2.61i.mm"

theorem addcomgi
  let cA: class A
  let cB: class B


  assert |- ( A + B ) = ( B + A )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    wa
    cA
    cB
    caddc
    co
    cB
    cA
    caddc
    co
    wceq
    cA
    cB
    addcom
    cA
    cB
    cc
    caddc
    cc
    cc
    cxp
    cc
    caddc
    ax-addf
    fdmi
    ndmovcom
    pm2.61i
end

include "wss.mm"
include "ccm.mm"
include "wbr.mm"
include "lecmi.mm"
include "ax-mp.mm"

theorem lecmii
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume pjoml2.1: |- A e. CH
  assume pjoml2.2: |- B e. CH
  assume lecmi.1: |- A C_ B


  assert |- A C_H B

  proof
    cA
    cB
    wss
    cA
    cB
    ccm
    wbr
    lecmi.1
    cA
    cB
    pjoml2.1
    pjoml2.2
    lecmi
    ax-mp
end

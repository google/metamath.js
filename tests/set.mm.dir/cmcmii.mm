include "ccm.mm"
include "wbr.mm"
include "cmcmi.mm"
include "mpbi.mm"

theorem cmcmii
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume pjoml2.1: |- A e. CH
  assume pjoml2.2: |- B e. CH
  assume cmcmi.1: |- A C_H B


  assert |- B C_H A

  proof
    cA
    cB
    ccm
    wbr
    cB
    cA
    ccm
    wbr
    cmcmi.1
    cA
    cB
    pjoml2.1
    pjoml2.2
    cmcmi
    mpbi
end

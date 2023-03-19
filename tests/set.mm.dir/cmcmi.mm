include "ccm.mm"
include "wbr.mm"
include "cmcmlem.mm"
include "impbii.mm"

theorem cmcmi
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume pjoml2.1: |- A e. CH
  assume pjoml2.2: |- B e. CH


  assert |- ( A C_H B <-> B C_H A )

  proof
    cA
    cB
    ccm
    wbr
    cB
    cA
    ccm
    wbr
    cA
    cB
    pjoml2.1
    pjoml2.2
    cmcmlem
    cB
    cA
    pjoml2.2
    pjoml2.1
    cmcmlem
    impbii
end

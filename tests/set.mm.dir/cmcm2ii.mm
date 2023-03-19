include "ccm.mm"
include "wbr.mm"
include "cort.mm"
include "cfv.mm"
include "cmcm2i.mm"
include "mpbi.mm"

theorem cmcm2ii
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume pjoml2.1: |- A e. CH
  assume pjoml2.2: |- B e. CH
  assume cmcmi.1: |- A C_H B


  assert |- A C_H ( _|_ ` B )

  proof
    cA
    cB
    ccm
    wbr
    cA
    cB
    cort
    cfv
    ccm
    wbr
    cmcmi.1
    cA
    cB
    pjoml2.1
    pjoml2.2
    cmcm2i
    mpbi
end

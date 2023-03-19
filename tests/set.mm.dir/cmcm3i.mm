include "ccm.mm"
include "wbr.mm"
include "cort.mm"
include "cfv.mm"
include "cmcm2i.mm"
include "cmcmi.mm"
include "choccli.mm"
include "3bitr4i.mm"

theorem cmcm3i
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume pjoml2.1: |- A e. CH
  assume pjoml2.2: |- B e. CH


  assert |- ( A C_H B <-> ( _|_ ` A ) C_H B )

  proof
    cB
    cA
    ccm
    wbr
    cB
    cA
    cort
    cfv
    #
    ccm
    wbr
    cA
    cB
    ccm
    wbr
    @0
    cB
    ccm
    wbr
    cB
    cA
    pjoml2.2
    pjoml2.1
    cmcm2i
    cA
    cB
    pjoml2.1
    pjoml2.2
    cmcmi
    @0
    cB
    cA
    pjoml2.1
    choccli
    pjoml2.2
    cmcmi
    3bitr4i
end

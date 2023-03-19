include "ccm.mm"
include "wbr.mm"
include "cort.mm"
include "cfv.mm"
include "cmcm2i.mm"
include "choccli.mm"
include "cmcm3i.mm"
include "bitri.mm"

theorem cmcm4i
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume pjoml2.1: |- A e. CH
  assume pjoml2.2: |- B e. CH


  assert |- ( A C_H B <-> ( _|_ ` A ) C_H ( _|_ ` B ) )

  proof
    cA
    cB
    ccm
    wbr
    cA
    cB
    cort
    cfv
    #
    ccm
    wbr
    cA
    cort
    cfv
    @0
    ccm
    wbr
    cA
    cB
    pjoml2.1
    pjoml2.2
    cmcm2i
    cA
    @0
    pjoml2.1
    cB
    pjoml2.2
    choccli
    cmcm3i
    bitri
end

include "ctvc.mm"
include "wcel.mm"
include "ctlm.mm"
include "csca.mm"
include "cfv.mm"
include "ctdrg.mm"
include "eqid.mm"
include "istvc.mm"
include "simplbi.mm"

theorem tvctlm
  let cW: class W


  assert |- ( W e. TopVec -> W e. TopMod )

  proof
    cW
    ctvc
    wcel
    cW
    ctlm
    wcel
    cW
    csca
    cfv
    #
    ctdrg
    wcel
    @0
    cW
    @0
    eqid
    istvc
    simplbi
end

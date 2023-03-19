include "ctvc.mm"
include "wcel.mm"
include "ctlm.mm"
include "clmod.mm"
include "tvctlm.mm"
include "tlmlmod.mm"
include "syl.mm"

theorem tvclmod
  let cW: class W


  assert |- ( W e. TopVec -> W e. LMod )

  proof
    cW
    ctvc
    wcel
    cW
    ctlm
    wcel
    cW
    clmod
    wcel
    cW
    tvctlm
    cW
    tlmlmod
    syl
end

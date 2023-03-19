include "ctlm.mm"
include "wcel.mm"
include "ctmd.mm"
include "ctps.mm"
include "tlmtmd.mm"
include "tmdtps.mm"
include "syl.mm"

theorem tlmtps
  let cW: class W


  assert |- ( W e. TopMod -> W e. TopSp )

  proof
    cW
    ctlm
    wcel
    cW
    ctmd
    wcel
    cW
    ctps
    wcel
    cW
    tlmtmd
    cW
    tmdtps
    syl
end

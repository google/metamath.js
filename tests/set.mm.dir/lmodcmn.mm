include "clmod.mm"
include "wcel.mm"
include "cabl.mm"
include "ccmn.mm"
include "lmodabl.mm"
include "ablcmn.mm"
include "syl.mm"

theorem lmodcmn
  let cW: class W
  let vx: setvar x
  let vy: setvar y


  assert |- ( W e. LMod -> W e. CMnd )

  proof
    cW
    clmod
    wcel
    cW
    cabl
    wcel
    cW
    ccmn
    wcel
    cW
    lmodabl
    cW
    ablcmn
    syl
end

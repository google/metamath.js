include "cclm.mm"
include "wcel.mm"
include "clmod.mm"
include "cabl.mm"
include "clmlmod.mm"
include "lmodabl.mm"
include "syl.mm"

theorem clmabl
  let cW: class W


  assert |- ( W e. CMod -> W e. Abel )

  proof
    cW
    cclm
    wcel
    cW
    clmod
    wcel
    cW
    cabl
    wcel
    cW
    clmlmod
    cW
    lmodabl
    syl
end

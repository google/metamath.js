include "crg.mm"
include "wcel.mm"
include "cabl.mm"
include "ccmn.mm"
include "ringabl.mm"
include "ablcmn.mm"
include "syl.mm"

theorem ringcmn
  let cR: class R


  assert |- ( R e. Ring -> R e. CMnd )

  proof
    cR
    crg
    wcel
    cR
    cabl
    wcel
    cR
    ccmn
    wcel
    cR
    ringabl
    cR
    ablcmn
    syl
end

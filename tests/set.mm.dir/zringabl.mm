include "zring.mm"
include "crg.mm"
include "wcel.mm"
include "cabl.mm"
include "zringring.mm"
include "ringabl.mm"
include "ax-mp.mm"

theorem zringabl



  assert |- ZZring e. Abel

  proof
    zring
    crg
    wcel
    zring
    cabl
    wcel
    zringring
    zring
    ringabl
    ax-mp
end

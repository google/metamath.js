include "zring.mm"
include "ccrg.mm"
include "wcel.mm"
include "crg.mm"
include "zringcrng.mm"
include "crngring.mm"
include "ax-mp.mm"

theorem zringring



  assert |- ZZring e. Ring

  proof
    zring
    ccrg
    wcel
    zring
    crg
    wcel
    zringcrng
    zring
    crngring
    ax-mp
end

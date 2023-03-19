include "c1.mm"
include "cn.mm"
include "wcel.mm"
include "cneg.mm"
include "cz.mm"
include "1nn.mm"
include "nnnegz.mm"
include "ax-mp.mm"

theorem neg1z



  assert |- -u 1 e. ZZ

  proof
    c1
    cn
    wcel
    c1
    cneg
    cz
    wcel
    1nn
    c1
    nnnegz
    ax-mp
end

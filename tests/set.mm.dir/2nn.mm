include "c2.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cn.mm"
include "df-2.mm"
include "wcel.mm"
include "1nn.mm"
include "peano2nn.mm"
include "ax-mp.mm"
include "eqeltri.mm"

theorem 2nn



  assert |- 2 e. NN

  proof
    c2
    c1
    c1
    caddc
    co
    #
    cn
    df-2
    c1
    cn
    wcel
    @0
    cn
    wcel
    1nn
    c1
    peano2nn
    ax-mp
    eqeltri
end

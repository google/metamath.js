include "c8.mm"
include "c7.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cn.mm"
include "df-8.mm"
include "wcel.mm"
include "7nn.mm"
include "peano2nn.mm"
include "ax-mp.mm"
include "eqeltri.mm"

theorem 8nn



  assert |- 8 e. NN

  proof
    c8
    c7
    c1
    caddc
    co
    #
    cn
    df-8
    c7
    cn
    wcel
    @0
    cn
    wcel
    7nn
    c7
    peano2nn
    ax-mp
    eqeltri
end

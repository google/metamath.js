include "c4.mm"
include "c3.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cn.mm"
include "df-4.mm"
include "wcel.mm"
include "3nn.mm"
include "peano2nn.mm"
include "ax-mp.mm"
include "eqeltri.mm"

theorem 4nn



  assert |- 4 e. NN

  proof
    c4
    c3
    c1
    caddc
    co
    #
    cn
    df-4
    c3
    cn
    wcel
    @0
    cn
    wcel
    3nn
    c3
    peano2nn
    ax-mp
    eqeltri
end

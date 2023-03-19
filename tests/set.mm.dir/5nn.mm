include "c5.mm"
include "c4.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cn.mm"
include "df-5.mm"
include "wcel.mm"
include "4nn.mm"
include "peano2nn.mm"
include "ax-mp.mm"
include "eqeltri.mm"

theorem 5nn



  assert |- 5 e. NN

  proof
    c5
    c4
    c1
    caddc
    co
    #
    cn
    df-5
    c4
    cn
    wcel
    @0
    cn
    wcel
    4nn
    c4
    peano2nn
    ax-mp
    eqeltri
end

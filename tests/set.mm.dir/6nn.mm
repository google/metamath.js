include "c6.mm"
include "c5.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cn.mm"
include "df-6.mm"
include "wcel.mm"
include "5nn.mm"
include "peano2nn.mm"
include "ax-mp.mm"
include "eqeltri.mm"

theorem 6nn



  assert |- 6 e. NN

  proof
    c6
    c5
    c1
    caddc
    co
    #
    cn
    df-6
    c5
    cn
    wcel
    @0
    cn
    wcel
    5nn
    c5
    peano2nn
    ax-mp
    eqeltri
end

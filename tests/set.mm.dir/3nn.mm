include "c3.mm"
include "c2.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cn.mm"
include "df-3.mm"
include "wcel.mm"
include "2nn.mm"
include "peano2nn.mm"
include "ax-mp.mm"
include "eqeltri.mm"

theorem 3nn



  assert |- 3 e. NN

  proof
    c3
    c2
    c1
    caddc
    co
    #
    cn
    df-3
    c2
    cn
    wcel
    @0
    cn
    wcel
    2nn
    c2
    peano2nn
    ax-mp
    eqeltri
end

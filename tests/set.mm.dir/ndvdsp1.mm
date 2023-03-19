include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cdvds.mm"
include "caddc.mm"
include "co.mm"
include "wn.mm"
include "wi.mm"
include "1nn.mm"
include "jctl.mm"
include "ndvdsadd.mm"
include "syl3an3.mm"

theorem ndvdsp1
  let cD: class D
  let cN: class N


  assert |- ( ( N e. ZZ /\ D e. NN /\ 1 < D ) -> ( D || N -> -. D || ( N + 1 ) ) )

  proof
    c1
    cD
    clt
    wbr
    #
    cN
    cz
    wcel
    cD
    cn
    wcel
    c1
    cn
    wcel
    #
    @0
    wa
    cD
    cN
    cdvds
    wbr
    cD
    cN
    c1
    caddc
    co
    cdvds
    wbr
    wn
    wi
    @0
    @1
    1nn
    jctl
    cD
    c1
    cN
    ndvdsadd
    syl3an3
end

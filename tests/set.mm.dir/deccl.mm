include "cdc.mm"
include "c9.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "cn0.mm"
include "df-dec.mm"
include "9nn0.mm"
include "1nn0.mm"
include "nn0addcli.mm"
include "numcl.mm"
include "eqeltri.mm"

theorem deccl
  let cA: class A
  let cB: class B
  assume deccl.1: |- A e. NN0
  assume deccl.2: |- B e. NN0


  assert |- ; A B e. NN0

  proof
    cA
    cB
    cdc
    c9
    c1
    caddc
    co
    #
    cA
    cmul
    co
    cB
    caddc
    co
    cn0
    cA
    cB
    df-dec
    cA
    cB
    @0
    c9
    c1
    9nn0
    1nn0
    nn0addcli
    deccl.1
    deccl.2
    numcl
    eqeltri
end

include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cn.mm"
include "wcel.mm"
include "peano2nn.mm"
include "ax-mp.mm"
include "eqeltri.mm"

theorem jm2.27dlem4
  let cA: class A
  let cB: class B
  assume jm2.27dlem3.1: |- A e. NN
  assume jm2.27dlem4.2: |- B = ( A + 1 )


  assert |- B e. NN

  proof
    cB
    cA
    c1
    caddc
    co
    #
    cn
    jm2.27dlem4.2
    cA
    cn
    wcel
    @0
    cn
    wcel
    jm2.27dlem3.1
    cA
    peano2nn
    ax-mp
    eqeltri
end

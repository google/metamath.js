include "c2.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "c4.mm"
include "c3.mm"
include "4nn0.mm"
include "2nn0.mm"
include "2p1e3.mm"
include "decbin2.mm"
include "eqcomi.mm"
include "numsuc.mm"

theorem decbin3
  let cA: class A
  assume decbin.1: |- A e. NN0


  assert |- ( ( 4 x. A ) + 3 ) = ( ( 2 x. ( ( 2 x. A ) + 1 ) ) + 1 )

  proof
    c2
    c2
    cA
    cmul
    co
    c1
    caddc
    co
    cmul
    co
    #
    c1
    caddc
    co
    c4
    cA
    cmul
    co
    #
    c3
    caddc
    co
    cA
    c2
    c3
    c4
    @0
    4nn0
    decbin.1
    2nn0
    2p1e3
    @1
    c2
    caddc
    co
    @0
    cA
    decbin.1
    decbin2
    eqcomi
    numsuc
    eqcomi
end

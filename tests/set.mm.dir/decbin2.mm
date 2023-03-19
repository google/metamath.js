include "c2.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "c4.mm"
include "2t1e2.mm"
include "oveq2i.mm"
include "2cn.mm"
include "nn0cni.mm"
include "mulcli.mm"
include "ax-1cn.mm"
include "adddii.mm"
include "decbin0.mm"
include "oveq1i.mm"
include "3eqtr4ri.mm"

theorem decbin2
  let cA: class A
  assume decbin.1: |- A e. NN0


  assert |- ( ( 4 x. A ) + 2 ) = ( 2 x. ( ( 2 x. A ) + 1 ) )

  proof
    c2
    c2
    cA
    cmul
    co
    #
    cmul
    co
    #
    c2
    c1
    cmul
    co
    #
    caddc
    co
    @1
    c2
    caddc
    co
    c2
    @0
    c1
    caddc
    co
    cmul
    co
    c4
    cA
    cmul
    co
    #
    c2
    caddc
    co
    @2
    c2
    @1
    caddc
    2t1e2
    oveq2i
    c2
    @0
    c1
    2cn
    c2
    cA
    2cn
    cA
    decbin.1
    nn0cni
    mulcli
    ax-1cn
    adddii
    @3
    @1
    c2
    caddc
    cA
    decbin.1
    decbin0
    oveq1i
    3eqtr4ri
end

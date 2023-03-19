include "c2.mm"
include "cmul.mm"
include "co.mm"
include "c4.mm"
include "2t2e4.mm"
include "oveq1i.mm"
include "2cn.mm"
include "nn0cni.mm"
include "mulassi.mm"
include "eqtr3i.mm"

theorem decbin0
  let cA: class A
  assume decbin.1: |- A e. NN0


  assert |- ( 4 x. A ) = ( 2 x. ( 2 x. A ) )

  proof
    c2
    c2
    cmul
    co
    #
    cA
    cmul
    co
    c4
    cA
    cmul
    co
    c2
    c2
    cA
    cmul
    co
    cmul
    co
    @0
    c4
    cA
    cmul
    2t2e4
    oveq1i
    c2
    c2
    cA
    2cn
    2cn
    cA
    decbin.1
    nn0cni
    mulassi
    eqtr3i
end

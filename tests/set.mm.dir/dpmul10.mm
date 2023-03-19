include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "caddc.mm"
include "cdp.mm"
include "recni.mm"
include "10nn.mm"
include "nncni.mm"
include "nnne0i.mm"
include "divcan2i.mm"
include "oveq2i.mm"
include "dpval2.mm"
include "cn0.mm"
include "wcel.mm"
include "cr.mm"
include "dpcl.mm"
include "mp2an.mm"
include "mulcomi.mm"
include "nn0cni.mm"
include "divcli.mm"
include "adddii.mm"
include "3eqtr3i.mm"
include "dfdec10.mm"
include "3eqtr4i.mm"

theorem dpmul10
  let cA: class A
  let cB: class B
  assume dpval2.a: |- A e. NN0
  assume dpval2.b: |- B e. RR


  assert |- ( ( A . B ) x. ; 1 0 ) = ; A B

  proof
    c1
    cc0
    cdc
    #
    cA
    cmul
    co
    #
    @0
    cB
    @0
    cdiv
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @1
    cB
    caddc
    co
    cA
    cB
    cdp
    co
    #
    @0
    cmul
    co
    #
    cA
    cB
    cdc
    @3
    cB
    @1
    caddc
    cB
    @0
    cB
    dpval2.b
    recni
    #
    @0
    10nn
    nncni
    #
    @0
    10nn
    nnne0i
    #
    divcan2i
    oveq2i
    @0
    @5
    cmul
    co
    @0
    cA
    @2
    caddc
    co
    #
    cmul
    co
    @6
    @4
    @5
    @10
    @0
    cmul
    cA
    cB
    dpval2.a
    dpval2.b
    dpval2
    oveq2i
    @0
    @5
    @8
    @5
    cA
    cn0
    wcel
    cB
    cr
    wcel
    @5
    cr
    wcel
    dpval2.a
    dpval2.b
    cA
    cB
    dpcl
    mp2an
    recni
    mulcomi
    @0
    cA
    @2
    @8
    cA
    dpval2.a
    nn0cni
    cB
    @0
    @7
    @8
    @9
    divcli
    adddii
    3eqtr3i
    cA
    cB
    dfdec10
    3eqtr4i
end

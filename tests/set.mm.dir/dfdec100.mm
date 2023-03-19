include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "dfdec10.mm"
include "oveq2i.mm"
include "cc.mm"
include "10nn0.mm"
include "dec0u.mm"
include "nn0cni.mm"
include "mulcli.mm"
include "eqeltrri.mm"
include "recni.mm"
include "addassi.mm"
include "adddii.mm"
include "mulassi.mm"
include "oveq1i.mm"
include "eqtr3i.mm"
include "3eqtri.mm"
include "eqtr2i.mm"
include "3eqtr2ri.mm"

theorem dfdec100
  let cA: class A
  let cB: class B
  let cC: class C
  assume dfdec100.a: |- A e. NN0
  assume dfdec100.b: |- B e. NN0
  assume dfdec100.c: |- C e. RR


  assert |- ; ; A B C = ( ( ; ; 1 0 0 x. A ) + ; B C )

  proof
    c1
    cc0
    cdc
    #
    cc0
    cdc
    #
    cA
    cmul
    co
    #
    cB
    cC
    cdc
    #
    caddc
    co
    @2
    @0
    cB
    cmul
    co
    #
    cC
    caddc
    co
    #
    caddc
    co
    @2
    @4
    caddc
    co
    #
    cC
    caddc
    co
    #
    cA
    cB
    cdc
    #
    cC
    cdc
    #
    @3
    @5
    @2
    caddc
    cB
    cC
    dfdec10
    oveq2i
    @2
    @4
    cC
    @1
    cA
    @0
    @0
    cmul
    co
    #
    @1
    cc
    @0
    10nn0
    dec0u
    #
    @0
    @0
    @0
    10nn0
    nn0cni
    #
    @12
    mulcli
    eqeltrri
    cA
    dfdec100.a
    nn0cni
    #
    mulcli
    @0
    cB
    @12
    cB
    dfdec100.b
    nn0cni
    #
    mulcli
    cC
    dfdec100.c
    recni
    addassi
    @9
    @0
    @8
    cmul
    co
    #
    cC
    caddc
    co
    @7
    @8
    cC
    dfdec10
    @15
    @6
    cC
    caddc
    @15
    @0
    @0
    cA
    cmul
    co
    #
    cB
    caddc
    co
    #
    cmul
    co
    @0
    @16
    cmul
    co
    #
    @4
    caddc
    co
    @6
    @8
    @17
    @0
    cmul
    cA
    cB
    dfdec10
    oveq2i
    @0
    @16
    cB
    @12
    @0
    cA
    @12
    @13
    mulcli
    @14
    adddii
    @18
    @2
    @4
    caddc
    @10
    cA
    cmul
    co
    @18
    @2
    @0
    @0
    cA
    @12
    @12
    @13
    mulassi
    @10
    @1
    cA
    cmul
    @11
    oveq1i
    eqtr3i
    oveq1i
    3eqtri
    oveq1i
    eqtr2i
    3eqtr2ri
end

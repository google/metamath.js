include "cdc.mm"
include "c1.mm"
include "cc0.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "c2.mm"
include "cexp.mm"
include "dfdec10.mm"
include "oveq2i.mm"
include "1nn.mm"
include "decnncl2.mm"
include "nncni.mm"
include "nn0cni.mm"
include "mulcli.mm"
include "adddii.mm"
include "eqtri.mm"
include "mulassi.mm"
include "eqcomi.mm"
include "sqvali.mm"
include "oveq1i.mm"

theorem 3dec
  let cA: class A
  let cB: class B
  let cC: class C
  assume 3dec.a: |- A e. NN0
  assume 3dec.b: |- B e. NN0


  assert |- ; ; A B C = ( ( ( ( ; 1 0 ^ 2 ) x. A ) + ( ; 1 0 x. B ) ) + C )

  proof
    cA
    cB
    cdc
    #
    cC
    cdc
    c1
    cc0
    cdc
    #
    @0
    cmul
    co
    #
    cC
    caddc
    co
    @1
    c2
    cexp
    co
    #
    cA
    cmul
    co
    #
    @1
    cB
    cmul
    co
    #
    caddc
    co
    #
    cC
    caddc
    co
    @0
    cC
    dfdec10
    @2
    @6
    cC
    caddc
    @2
    @1
    @1
    cA
    cmul
    co
    #
    cmul
    co
    #
    @5
    caddc
    co
    #
    @6
    @2
    @1
    @7
    cB
    caddc
    co
    #
    cmul
    co
    @9
    @0
    @10
    @1
    cmul
    cA
    cB
    dfdec10
    oveq2i
    @1
    @7
    cB
    @1
    c1
    1nn
    decnncl2
    nncni
    #
    @1
    cA
    @11
    cA
    3dec.a
    nn0cni
    #
    mulcli
    cB
    3dec.b
    nn0cni
    adddii
    eqtri
    @8
    @4
    @5
    caddc
    @8
    @1
    @1
    cmul
    co
    #
    cA
    cmul
    co
    #
    @4
    @14
    @8
    @1
    @1
    cA
    @11
    @11
    @12
    mulassi
    eqcomi
    @13
    @3
    cA
    cmul
    @3
    @13
    @1
    @11
    sqvali
    eqcomi
    oveq1i
    eqtri
    oveq1i
    eqtri
    oveq1i
    eqtri
end

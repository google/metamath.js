include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "10nn0.mm"
include "numexp1.mm"
include "oveq2i.mm"
include "nn0cni.mm"
include "mulcomi.mm"
include "eqtr4i.mm"
include "oveq1i.mm"
include "dfdec10.mm"

theorem decsplit1
  let cA: class A
  let cB: class B
  assume decsplit0.1: |- A e. NN0


  assert |- ( ( A x. ( ; 1 0 ^ 1 ) ) + B ) = ; A B

  proof
    cA
    c1
    cc0
    cdc
    #
    c1
    cexp
    co
    #
    cmul
    co
    #
    cB
    caddc
    co
    @0
    cA
    cmul
    co
    #
    cB
    caddc
    co
    cA
    cB
    cdc
    @2
    @3
    cB
    caddc
    @2
    cA
    @0
    cmul
    co
    @3
    @1
    @0
    cA
    cmul
    @0
    10nn0
    numexp1
    oveq2i
    @0
    cA
    @0
    10nn0
    nn0cni
    cA
    decsplit0.1
    nn0cni
    mulcomi
    eqtr4i
    oveq1i
    cA
    cB
    dfdec10
    eqtr4i
end

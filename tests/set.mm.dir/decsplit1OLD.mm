include "c10.mm"
include "c1.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "cdc.mm"
include "10nn0OLD.mm"
include "numexp1.mm"
include "oveq2i.mm"
include "nn0cni.mm"
include "mulcomi.mm"
include "eqtr4i.mm"
include "oveq1i.mm"
include "dfdecOLD.mm"

theorem decsplit1OLD
  let cA: class A
  let cB: class B
  assume decsplit0OLD.1: |- A e. NN0


  assert |- ( ( A x. ( 10 ^ 1 ) ) + B ) = ; A B

  proof
    cA
    c10
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
    c10
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
    @1
    @2
    cB
    caddc
    @1
    cA
    c10
    cmul
    co
    @2
    @0
    c10
    cA
    cmul
    c10
    10nn0OLD
    numexp1
    oveq2i
    c10
    cA
    c10
    10nn0OLD
    nn0cni
    cA
    decsplit0OLD.1
    nn0cni
    mulcomi
    eqtr4i
    oveq1i
    cA
    cB
    dfdecOLD
    eqtr4i
end

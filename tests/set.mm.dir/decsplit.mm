include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "10nn0.mm"
include "nn0expcli.mm"
include "nn0mulcli.mm"
include "nn0cni.mm"
include "addassi.mm"
include "adddii.mm"
include "oveq2i.mm"
include "eqtr3i.mm"
include "oveq1i.mm"
include "mulcomi.mm"
include "numexpp1.mm"
include "mul12i.mm"
include "eqtri.mm"
include "dfdec10.mm"
include "oveq12i.mm"
include "3eqtr4i.mm"

theorem decsplit
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cM: class M
  let cN: class N
  assume decsplit0.1: |- A e. NN0
  assume decsplit.2: |- B e. NN0
  assume decsplit.3: |- D e. NN0
  assume decsplit.4: |- M e. NN0
  assume decsplit.5: |- ( M + 1 ) = N
  assume decsplit.6: |- ( ( A x. ( ; 1 0 ^ M ) ) + B ) = C


  assert |- ( ( A x. ( ; 1 0 ^ N ) ) + ; B D ) = ; C D

  proof
    c1
    cc0
    cdc
    #
    cA
    @0
    cM
    cexp
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    @0
    cB
    cmul
    co
    #
    cD
    caddc
    co
    #
    caddc
    co
    #
    @0
    cC
    cmul
    co
    #
    cD
    caddc
    co
    #
    cA
    @0
    cN
    cexp
    co
    #
    cmul
    co
    #
    cB
    cD
    cdc
    #
    caddc
    co
    cC
    cD
    cdc
    @3
    @4
    caddc
    co
    #
    cD
    caddc
    co
    @6
    @8
    @3
    @4
    cD
    @3
    @0
    @2
    10nn0
    cA
    @1
    decsplit0.1
    @0
    cM
    10nn0
    decsplit.4
    nn0expcli
    #
    nn0mulcli
    #
    nn0mulcli
    nn0cni
    @4
    @0
    cB
    10nn0
    decsplit.2
    nn0mulcli
    nn0cni
    cD
    decsplit.3
    nn0cni
    addassi
    @12
    @7
    cD
    caddc
    @0
    @2
    cB
    caddc
    co
    #
    cmul
    co
    @12
    @7
    @0
    @2
    cB
    @0
    10nn0
    nn0cni
    #
    @2
    @14
    nn0cni
    cB
    decsplit.2
    nn0cni
    adddii
    @15
    cC
    @0
    cmul
    decsplit.6
    oveq2i
    eqtr3i
    oveq1i
    eqtr3i
    @10
    @3
    @11
    @5
    caddc
    @10
    cA
    @0
    @1
    cmul
    co
    #
    cmul
    co
    @3
    @9
    @17
    cA
    cmul
    @0
    @17
    cM
    cN
    10nn0
    decsplit.4
    decsplit.5
    @1
    @0
    @1
    @13
    nn0cni
    #
    @16
    mulcomi
    numexpp1
    oveq2i
    cA
    @0
    @1
    cA
    decsplit0.1
    nn0cni
    @16
    @18
    mul12i
    eqtri
    cB
    cD
    dfdec10
    oveq12i
    cC
    cD
    dfdec10
    3eqtr4i
end

include "c10.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "cdc.mm"
include "10nn0OLD.mm"
include "nn0cni.mm"
include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "expcl.mm"
include "mp2an.mm"
include "mulcli.mm"
include "nn0mulcli.mm"
include "addassi.mm"
include "adddii.mm"
include "oveq2i.mm"
include "eqtr3i.mm"
include "oveq1i.mm"
include "mulcomi.mm"
include "numexpp1.mm"
include "mul12i.mm"
include "eqtri.mm"
include "dfdecOLD.mm"
include "oveq12i.mm"
include "3eqtr4i.mm"

theorem decsplitOLD
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cM: class M
  let cN: class N
  assume decsplit0OLD.1: |- A e. NN0
  assume decsplitOLD.2: |- B e. NN0
  assume decsplitOLD.3: |- D e. NN0
  assume decsplitOLD.4: |- M e. NN0
  assume decsplitOLD.5: |- ( M + 1 ) = N
  assume decsplitOLD.6: |- ( ( A x. ( 10 ^ M ) ) + B ) = C


  assert |- ( ( A x. ( 10 ^ N ) ) + ; B D ) = ; C D

  proof
    c10
    cA
    c10
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
    c10
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
    c10
    cC
    cmul
    co
    #
    cD
    caddc
    co
    #
    cA
    c10
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
    @2
    @3
    caddc
    co
    #
    cD
    caddc
    co
    @5
    @7
    @2
    @3
    cD
    c10
    @1
    c10
    10nn0OLD
    nn0cni
    #
    cA
    @0
    cA
    decsplit0OLD.1
    nn0cni
    #
    c10
    cc
    wcel
    cM
    cn0
    wcel
    @0
    cc
    wcel
    @12
    decsplitOLD.4
    c10
    cM
    expcl
    mp2an
    #
    mulcli
    #
    mulcli
    @3
    c10
    cB
    10nn0OLD
    decsplitOLD.2
    nn0mulcli
    nn0cni
    cD
    decsplitOLD.3
    nn0cni
    addassi
    @11
    @6
    cD
    caddc
    c10
    @1
    cB
    caddc
    co
    #
    cmul
    co
    @11
    @6
    c10
    @1
    cB
    @12
    @15
    cB
    decsplitOLD.2
    nn0cni
    adddii
    @16
    cC
    c10
    cmul
    decsplitOLD.6
    oveq2i
    eqtr3i
    oveq1i
    eqtr3i
    @9
    @2
    @10
    @4
    caddc
    @9
    cA
    c10
    @0
    cmul
    co
    #
    cmul
    co
    @2
    @8
    @17
    cA
    cmul
    c10
    @17
    cM
    cN
    10nn0OLD
    decsplitOLD.4
    decsplitOLD.5
    @0
    c10
    @14
    @12
    mulcomi
    numexpp1
    oveq2i
    cA
    c10
    @0
    @13
    @12
    @14
    mul12i
    eqtri
    cB
    cD
    dfdecOLD
    oveq12i
    cC
    cD
    dfdecOLD
    3eqtr4i
end

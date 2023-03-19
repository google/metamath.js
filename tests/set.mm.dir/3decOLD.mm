include "cdc.mm"
include "c10.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "c2.mm"
include "cexp.mm"
include "dfdecOLD.mm"
include "oveq2i.mm"
include "10nnOLD.mm"
include "nncni.mm"
include "nn0cni.mm"
include "mulcli.mm"
include "adddii.mm"
include "eqtri.mm"
include "mulassi.mm"
include "eqcomi.mm"
include "sqvali.mm"
include "oveq1i.mm"

theorem 3decOLD
  let cA: class A
  let cB: class B
  let cC: class C
  assume 3decOLD.a: |- A e. NN0
  assume 3decOLD.b: |- B e. NN0


  assert |- ; ; A B C = ( ( ( ( 10 ^ 2 ) x. A ) + ( 10 x. B ) ) + C )

  proof
    cA
    cB
    cdc
    #
    cC
    cdc
    c10
    @0
    cmul
    co
    #
    cC
    caddc
    co
    c10
    c2
    cexp
    co
    #
    cA
    cmul
    co
    #
    c10
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
    dfdecOLD
    @1
    @5
    cC
    caddc
    @1
    c10
    c10
    cA
    cmul
    co
    #
    cmul
    co
    #
    @4
    caddc
    co
    #
    @5
    @1
    c10
    @6
    cB
    caddc
    co
    #
    cmul
    co
    @8
    @0
    @9
    c10
    cmul
    cA
    cB
    dfdecOLD
    oveq2i
    c10
    @6
    cB
    c10
    10nnOLD
    nncni
    #
    c10
    cA
    @10
    cA
    3decOLD.a
    nn0cni
    #
    mulcli
    cB
    3decOLD.b
    nn0cni
    adddii
    eqtri
    @7
    @3
    @4
    caddc
    @7
    c10
    c10
    cmul
    co
    #
    cA
    cmul
    co
    #
    @3
    @13
    @7
    c10
    c10
    cA
    @10
    @10
    @11
    mulassi
    eqcomi
    @12
    @2
    cA
    cmul
    @2
    @12
    c10
    @10
    sqvali
    eqcomi
    oveq1i
    eqtri
    oveq1i
    eqtri
    oveq1i
    eqtri
end

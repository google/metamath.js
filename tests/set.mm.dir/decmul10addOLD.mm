include "cdc.mm"
include "cmul.mm"
include "co.mm"
include "c10.mm"
include "caddc.mm"
include "cc0.mm"
include "dfdecOLD.mm"
include "oveq2i.mm"
include "nn0cni.mm"
include "10nn0OLD.mm"
include "nn0mulcli.mm"
include "adddii.mm"
include "mul12i.mm"
include "dec0uOLD.mm"
include "eqcomi.mm"
include "deceq1i.mm"
include "3eqtri.mm"
include "oveq12i.mm"

theorem decmul10addOLD
  let cA: class A
  let cB: class B
  let cE: class E
  let cF: class F
  let cM: class M
  assume decmul10add.1: |- A e. NN0
  assume decmul10add.2: |- B e. NN0
  assume decmul10add.3: |- M e. NN0
  assume decmul10add.4: |- E = ( M x. A )
  assume decmul10add.5: |- F = ( M x. B )


  assert |- ( M x. ; A B ) = ( ; E 0 + F )

  proof
    cM
    cA
    cB
    cdc
    #
    cmul
    co
    cM
    c10
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
    cM
    @1
    cmul
    co
    #
    cM
    cB
    cmul
    co
    #
    caddc
    co
    cE
    cc0
    cdc
    #
    cF
    caddc
    co
    @0
    @2
    cM
    cmul
    cA
    cB
    dfdecOLD
    oveq2i
    cM
    @1
    cB
    cM
    decmul10add.3
    nn0cni
    #
    @1
    c10
    cA
    10nn0OLD
    decmul10add.1
    nn0mulcli
    nn0cni
    cB
    decmul10add.2
    nn0cni
    adddii
    @3
    @5
    @4
    cF
    caddc
    @3
    c10
    cM
    cA
    cmul
    co
    #
    cmul
    co
    @7
    cc0
    cdc
    @5
    cM
    c10
    cA
    @6
    c10
    10nn0OLD
    nn0cni
    cA
    decmul10add.1
    nn0cni
    mul12i
    @7
    cM
    cA
    decmul10add.3
    decmul10add.1
    nn0mulcli
    dec0uOLD
    @7
    cE
    cc0
    cE
    @7
    decmul10add.4
    eqcomi
    deceq1i
    3eqtri
    cF
    @4
    decmul10add.5
    eqcomi
    oveq12i
    3eqtri
end

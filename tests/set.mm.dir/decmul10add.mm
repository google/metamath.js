include "cdc.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "cc0.mm"
include "caddc.mm"
include "dfdec10.mm"
include "oveq2i.mm"
include "nn0cni.mm"
include "10nn0.mm"
include "nn0mulcli.mm"
include "adddii.mm"
include "mul12i.mm"
include "dec0u.mm"
include "eqcomi.mm"
include "deceq1i.mm"
include "3eqtri.mm"
include "oveq12i.mm"

theorem decmul10add
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
    c1
    cc0
    cdc
    #
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
    @2
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
    @3
    cM
    cmul
    cA
    cB
    dfdec10
    oveq2i
    cM
    @2
    cB
    cM
    decmul10add.3
    nn0cni
    #
    @2
    @1
    cA
    10nn0
    decmul10add.1
    nn0mulcli
    nn0cni
    cB
    decmul10add.2
    nn0cni
    adddii
    @4
    @6
    @5
    cF
    caddc
    @4
    @1
    cM
    cA
    cmul
    co
    #
    cmul
    co
    @8
    cc0
    cdc
    @6
    cM
    @1
    cA
    @7
    @1
    10nn0
    nn0cni
    cA
    decmul10add.1
    nn0cni
    mul12i
    @8
    cM
    cA
    decmul10add.3
    decmul10add.1
    nn0mulcli
    dec0u
    @8
    cE
    cc0
    cE
    @8
    decmul10add.4
    eqcomi
    deceq1i
    3eqtri
    cF
    @5
    decmul10add.5
    eqcomi
    oveq12i
    3eqtri
end

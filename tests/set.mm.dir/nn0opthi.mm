include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "wa.mm"
include "wne.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "nn0addcli.mm"
include "nn0rei.mm"
include "lttri2i.mm"
include "nn0opthlem2.mm"
include "necomd.mm"
include "jaoi.mm"
include "sylbi.mm"
include "necon4i.mm"
include "id.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "nn0cni.mm"
include "mulcli.mm"
include "addcani.mm"
include "sylib.mm"
include "oveq2d.mm"
include "addcan2i.mm"
include "jca.mm"
include "oveq12.mm"
include "simpr.mm"
include "impbii.mm"

theorem nn0opthi
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume nn0opth.1: |- A e. NN0
  assume nn0opth.2: |- B e. NN0
  assume nn0opth.3: |- C e. NN0
  assume nn0opth.4: |- D e. NN0


  assert |- ( ( ( ( A + B ) x. ( A + B ) ) + B ) = ( ( ( C + D ) x. ( C + D ) ) + D ) <-> ( A = C /\ B = D ) )

  proof
    cA
    cB
    caddc
    co
    #
    @0
    cmul
    co
    #
    cB
    caddc
    co
    #
    cC
    cD
    caddc
    co
    #
    @3
    cmul
    co
    #
    cD
    caddc
    co
    #
    wceq
    #
    cA
    cC
    wceq
    #
    cB
    cD
    wceq
    #
    wa
    #
    @6
    @7
    @8
    @6
    @0
    cC
    cB
    caddc
    co
    #
    wceq
    @7
    @6
    @0
    @3
    @10
    @0
    @3
    @2
    @5
    @0
    @3
    wne
    @0
    @3
    clt
    wbr
    #
    @3
    @0
    clt
    wbr
    #
    wo
    @2
    @5
    wne
    #
    @0
    @3
    @0
    cA
    cB
    nn0opth.1
    nn0opth.2
    nn0addcli
    #
    nn0rei
    @3
    cC
    cD
    nn0opth.3
    nn0opth.4
    nn0addcli
    #
    nn0rei
    lttri2i
    @11
    @13
    @12
    @11
    @5
    @2
    cA
    cB
    @3
    cD
    nn0opth.1
    nn0opth.2
    @15
    nn0opth.4
    nn0opthlem2
    necomd
    cC
    cD
    @0
    cB
    nn0opth.3
    nn0opth.4
    @14
    nn0opth.2
    nn0opthlem2
    jaoi
    sylbi
    necon4i
    #
    @6
    cB
    cD
    cC
    caddc
    @6
    @2
    @1
    cD
    caddc
    co
    #
    wceq
    @8
    @6
    @2
    @5
    @17
    @6
    id
    @6
    @1
    @4
    cD
    caddc
    @6
    @0
    @3
    @0
    @3
    cmul
    @16
    @16
    oveq12d
    oveq1d
    eqtr4d
    @1
    cB
    cD
    @0
    @0
    @0
    @14
    nn0cni
    #
    @18
    mulcli
    cB
    nn0opth.2
    nn0cni
    #
    cD
    nn0opth.4
    nn0cni
    addcani
    sylib
    #
    oveq2d
    eqtr4d
    cA
    cC
    cB
    cA
    nn0opth.1
    nn0cni
    cC
    nn0opth.3
    nn0cni
    @19
    addcan2i
    sylib
    @20
    jca
    @9
    @1
    @4
    cB
    cD
    caddc
    @9
    @0
    @3
    @0
    @3
    cmul
    cA
    cC
    cB
    cD
    caddc
    oveq12
    #
    @21
    oveq12d
    @7
    @8
    simpr
    oveq12d
    impbii
end

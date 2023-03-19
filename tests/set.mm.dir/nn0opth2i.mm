include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "wceq.mm"
include "cmul.mm"
include "wa.mm"
include "nn0cni.mm"
include "addcli.mm"
include "sqvali.mm"
include "oveq1i.mm"
include "eqeq12i.mm"
include "nn0opthi.mm"
include "bitri.mm"

theorem nn0opth2i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume nn0opth.1: |- A e. NN0
  assume nn0opth.2: |- B e. NN0
  assume nn0opth.3: |- C e. NN0
  assume nn0opth.4: |- D e. NN0


  assert |- ( ( ( ( A + B ) ^ 2 ) + B ) = ( ( ( C + D ) ^ 2 ) + D ) <-> ( A = C /\ B = D ) )

  proof
    cA
    cB
    caddc
    co
    #
    c2
    cexp
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
    c2
    cexp
    co
    #
    cD
    caddc
    co
    #
    wceq
    @0
    @0
    cmul
    co
    #
    cB
    caddc
    co
    #
    @3
    @3
    cmul
    co
    #
    cD
    caddc
    co
    #
    wceq
    cA
    cC
    wceq
    cB
    cD
    wceq
    wa
    @2
    @7
    @5
    @9
    @1
    @6
    cB
    caddc
    @0
    cA
    cB
    cA
    nn0opth.1
    nn0cni
    cB
    nn0opth.2
    nn0cni
    addcli
    sqvali
    oveq1i
    @4
    @8
    cD
    caddc
    @3
    cC
    cD
    cC
    nn0opth.3
    nn0cni
    cD
    nn0opth.4
    nn0cni
    addcli
    sqvali
    oveq1i
    eqeq12i
    cA
    cB
    cC
    cD
    nn0opth.1
    nn0opth.2
    nn0opth.3
    nn0opth.4
    nn0opthi
    bitri
end

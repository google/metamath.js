include "cun.mm"
include "cfn.mm"
include "wcel.mm"
include "wss.mm"
include "ssun1.mm"
include "ssfi.mm"
include "mpan2.mm"
include "ssun2.mm"
include "jca.mm"

theorem unfir
  let cA: class A
  let cB: class B


  assert |- ( ( A u. B ) e. Fin -> ( A e. Fin /\ B e. Fin ) )

  proof
    cA
    cB
    cun
    #
    cfn
    wcel
    #
    cA
    cfn
    wcel
    #
    cB
    cfn
    wcel
    #
    @1
    cA
    @0
    wss
    @2
    cA
    cB
    ssun1
    @0
    cA
    ssfi
    mpan2
    @1
    cB
    @0
    wss
    @3
    cB
    cA
    ssun2
    @0
    cB
    ssfi
    mpan2
    jca
end

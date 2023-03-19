include "chil.mm"
include "wcel.mm"
include "csn.mm"
include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "snssi.mm"
include "ococss.mm"
include "syl.mm"
include "snssg.mm"
include "mpbird.mm"

theorem h1did
  let cA: class A


  assert |- ( A e. ~H -> A e. ( _|_ ` ( _|_ ` { A } ) ) )

  proof
    cA
    chil
    wcel
    #
    cA
    cA
    csn
    #
    cort
    cfv
    cort
    cfv
    #
    wcel
    @1
    @2
    wss
    #
    @0
    @1
    chil
    wss
    @3
    cA
    chil
    snssi
    @1
    ococss
    syl
    cA
    @2
    chil
    snssg
    mpbird
end

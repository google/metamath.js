include "wss.mm"
include "cun.mm"
include "ssun1.mm"
include "sstr2.mm"
include "mpi.mm"

theorem ssun3
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A C_ B -> A C_ ( B u. C ) )

  proof
    cA
    cB
    wss
    cB
    cB
    cC
    cun
    #
    wss
    cA
    @0
    wss
    cB
    cC
    ssun1
    cA
    cB
    @0
    sstr2
    mpi
end

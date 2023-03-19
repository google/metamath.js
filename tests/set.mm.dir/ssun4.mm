include "wss.mm"
include "cun.mm"
include "ssun2.mm"
include "sstr2.mm"
include "mpi.mm"

theorem ssun4
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A C_ B -> A C_ ( C u. B ) )

  proof
    cA
    cB
    wss
    cB
    cC
    cB
    cun
    #
    wss
    cA
    @0
    wss
    cB
    cC
    ssun2
    cA
    cB
    @0
    sstr2
    mpi
end

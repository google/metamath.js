include "wcel.mm"
include "c0.mm"
include "wss.mm"
include "cdom.mm"
include "wbr.mm"
include "0ss.mm"
include "ssdomg.mm"
include "mpi.mm"

theorem 0domg
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> (/) ~<_ A )

  proof
    cA
    cV
    wcel
    c0
    cA
    wss
    c0
    cA
    cdom
    wbr
    cA
    0ss
    c0
    cA
    cV
    ssdomg
    mpi
end

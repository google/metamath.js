include "c0.mm"
include "wceq.mm"
include "wss.mm"
include "0ss.mm"
include "eqss.mm"
include "mpbiran2.mm"
include "bicomi.mm"

theorem ss0b
  let cA: class A


  assert |- ( A C_ (/) <-> A = (/) )

  proof
    cA
    c0
    wceq
    #
    cA
    c0
    wss
    #
    @0
    @1
    c0
    cA
    wss
    cA
    0ss
    cA
    c0
    eqss
    mpbiran2
    bicomi
end

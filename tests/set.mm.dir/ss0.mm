include "c0.mm"
include "wss.mm"
include "wceq.mm"
include "ss0b.mm"
include "biimpi.mm"

theorem ss0
  param cA: class A


  assert |- ( A C_ (/) -> A = (/) )

  proof
    cA
    c0
    wss
    cA
    c0
    wceq
    cA
    ss0b
    biimpi
end

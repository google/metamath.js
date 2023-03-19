include "cdif.mm"
include "c0.mm"
include "difid.mm"
include "difeq2i.mm"
include "difdif.mm"
include "eqtr3i.mm"

theorem dif0
  let cA: class A


  assert |- ( A \ (/) ) = A

  proof
    cA
    cA
    cA
    cdif
    #
    cdif
    cA
    c0
    cdif
    cA
    @0
    c0
    cA
    cA
    difid
    difeq2i
    cA
    cA
    difdif
    eqtr3i
end

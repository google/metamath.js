include "com.mm"
include "con0.mm"
include "omsson.mm"
include "sseli.mm"

theorem nnon
  let cA: class A


  assert |- ( A e. _om -> A e. On )

  proof
    com
    con0
    cA
    omsson
    sseli
end

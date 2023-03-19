include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "crnk.mm"
include "rankf.mm"
include "0elon.mm"
include "f0cli.mm"

theorem rankon
  let cA: class A


  assert |- ( rank ` A ) e. On

  proof
    cr1
    con0
    cima
    cuni
    con0
    cA
    crnk
    rankf
    0elon
    f0cli
end

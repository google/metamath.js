include "cneg.mm"
include "cc0.mm"
include "cmin.mm"
include "df-neg.mm"
include "ovexi.mm"

theorem negex
  let cA: class A


  assert |- -u A e. _V

  proof
    cA
    cneg
    cc0
    cA
    cmin
    cA
    df-neg
    ovexi
end

include "cfv.mm"
include "cvv.mm"
include "wcel.mm"
include "fvex.mm"
include "a1i.mm"

theorem fvexd
  let wph: wff ph
  let cA: class A
  let cF: class F


  assert |- ( ph -> ( F ` A ) e. _V )

  proof
    cA
    cF
    cfv
    cvv
    wcel
    wph
    cA
    cF
    fvex
    a1i
end

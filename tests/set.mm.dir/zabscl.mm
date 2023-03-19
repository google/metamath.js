include "cz.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "nn0abscl.mm"
include "nn0zd.mm"

theorem zabscl
  let cA: class A


  assert |- ( A e. ZZ -> ( abs ` A ) e. ZZ )

  proof
    cA
    cz
    wcel
    cA
    cabs
    cfv
    cA
    nn0abscl
    nn0zd
end

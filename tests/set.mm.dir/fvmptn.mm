include "nfcv.mm"
include "fvmptnf.mm"

theorem fvmptn
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  assume fvmptn.1: |- ( x = D -> B = C )
  assume fvmptn.2: |- F = ( x e. A |-> B )

  disjoint A x
  disjoint C x
  disjoint D x
  assert |- ( -. C e. _V -> ( F ` D ) = (/) )

  proof
    vx
    cD
    cB
    cC
    cA
    cF
    vx
    cD
    nfcv
    vx
    cC
    nfcv
    fvmptn.1
    fvmptn.2
    fvmptnf
end

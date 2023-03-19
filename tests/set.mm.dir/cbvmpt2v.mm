include "nfcv.mm"
include "weq.mm"
include "sylan9eq.mm"
include "cbvmpt2.mm"

theorem cbvmpt2v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  assume cbvmpt2v.1: |- ( x = z -> C = E )
  assume cbvmpt2v.2: |- ( y = w -> E = D )

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C w
  disjoint C z
  disjoint D x
  disjoint D y
  assert |- ( x e. A , y e. B |-> C ) = ( z e. A , w e. B |-> D )

  proof
    vx
    vy
    vz
    vw
    cA
    cB
    cC
    cD
    vz
    cC
    nfcv
    vw
    cC
    nfcv
    vx
    cD
    nfcv
    vy
    cD
    nfcv
    vx
    vz
    weq
    vy
    vw
    weq
    cC
    cE
    cD
    cbvmpt2v.1
    cbvmpt2v.2
    sylan9eq
    cbvmpt2
end

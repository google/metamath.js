include "nfcv.mm"
include "weq.mm"
include "eqidd.mm"
include "cbvmpt2x.mm"

theorem cbvmpt2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume cbvmpt2.1: |- F/_ z C
  assume cbvmpt2.2: |- F/_ w C
  assume cbvmpt2.3: |- F/_ x D
  assume cbvmpt2.4: |- F/_ y D
  assume cbvmpt2.5: |- ( ( x = z /\ y = w ) -> C = D )

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
  assert |- ( x e. A , y e. B |-> C ) = ( z e. A , w e. B |-> D )

  proof
    vx
    vy
    vz
    vw
    cA
    cB
    cC
    cB
    cD
    vz
    cB
    nfcv
    vx
    cB
    nfcv
    cbvmpt2.1
    cbvmpt2.2
    cbvmpt2.3
    cbvmpt2.4
    vx
    vz
    weq
    cB
    eqidd
    cbvmpt2.5
    cbvmpt2x
end

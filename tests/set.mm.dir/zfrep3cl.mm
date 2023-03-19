include "nfcv.mm"
include "zfrepclf.mm"

theorem zfrep3cl
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  assume zfrep3cl.1: |- A e. _V
  assume zfrep3cl.2: |- ( x e. A -> E. z A. y ( ph -> y = z ) )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint ph z
  assert |- E. z A. y ( y e. z <-> E. x ( x e. A /\ ph ) )

  proof
    wph
    vx
    vy
    vz
    cA
    vx
    cA
    nfcv
    zfrep3cl.1
    zfrep3cl.2
    zfrepclf
end

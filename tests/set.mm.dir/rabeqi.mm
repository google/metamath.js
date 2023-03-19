include "nfcv.mm"
include "rabeqif.mm"

theorem rabeqi
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rabeqi.1: |- A = B

  disjoint A x
  disjoint B x
  assert |- { x e. A | ph } = { x e. B | ph }

  proof
    wph
    vx
    cA
    cB
    vx
    cA
    nfcv
    vx
    cB
    nfcv
    rabeqi.1
    rabeqif
end

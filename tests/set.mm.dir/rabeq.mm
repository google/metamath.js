include "nfcv.mm"
include "rabeqf.mm"

theorem rabeq
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A = B -> { x e. A | ph } = { x e. B | ph } )

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
    rabeqf
end

include "nfcv.mm"
include "rabeqf.mm"

theorem rabeq
  param wph: wff ph
  param vx: setvar x
  param cA: class A
  param cB: class B

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

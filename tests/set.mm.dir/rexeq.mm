include "nfcv.mm"
include "rexeqf.mm"

theorem rexeq
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A = B -> ( E. x e. A ph <-> E. x e. B ph ) )

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
    rexeqf
end

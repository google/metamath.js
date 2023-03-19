include "nfcv.mm"
include "raleqf.mm"

theorem raleq
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A = B -> ( A. x e. A ph <-> A. x e. B ph ) )

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
    raleqf
end

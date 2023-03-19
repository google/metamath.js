include "nfv.mm"
include "r19.3rz.mm"

theorem r19.3rzv
  let wph: wff ph
  let vx: setvar x
  let cA: class A

  disjoint A x
  disjoint ph x
  assert |- ( A =/= (/) -> ( ph <-> A. x e. A ph ) )

  proof
    wph
    vx
    cA
    wph
    vx
    nfv
    r19.3rz
end

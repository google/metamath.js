include "nfv.mm"
include "r19.28z.mm"

theorem r19.28zv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A

  disjoint A x
  disjoint ph x
  assert |- ( A =/= (/) -> ( A. x e. A ( ph /\ ps ) <-> ( ph /\ A. x e. A ps ) ) )

  proof
    wph
    wps
    vx
    cA
    wph
    vx
    nfv
    r19.28z
end

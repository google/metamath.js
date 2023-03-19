include "nfv.mm"
include "r19.27z.mm"

theorem r19.27zv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A

  disjoint A x
  disjoint ps x
  assert |- ( A =/= (/) -> ( A. x e. A ( ph /\ ps ) <-> ( A. x e. A ph /\ ps ) ) )

  proof
    wph
    wps
    vx
    cA
    wps
    vx
    nfv
    r19.27z
end

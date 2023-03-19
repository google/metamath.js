include "nfv.mm"
include "r19.29af.mm"

theorem r19.29a
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume r19.29a.1: |- ( ( ( ph /\ x e. A ) /\ ps ) -> ch )
  assume r19.29a.2: |- ( ph -> E. x e. A ps )

  disjoint ch x
  disjoint ph x
  assert |- ( ph -> ch )

  proof
    wph
    wps
    wch
    vx
    cA
    wph
    vx
    nfv
    r19.29a.1
    r19.29a.2
    r19.29af
end

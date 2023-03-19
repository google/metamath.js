include "nfv.mm"
include "r19.29af2.mm"

theorem r19.29af
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume r19.29af.0: |- F/ x ph
  assume r19.29af.1: |- ( ( ( ph /\ x e. A ) /\ ps ) -> ch )
  assume r19.29af.2: |- ( ph -> E. x e. A ps )

  disjoint ch x
  assert |- ( ph -> ch )

  proof
    wph
    wps
    wch
    vx
    cA
    r19.29af.0
    wch
    vx
    nfv
    r19.29af.1
    r19.29af.2
    r19.29af2
end

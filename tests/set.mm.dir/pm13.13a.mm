include "cv.mm"
include "wceq.mm"
include "wsbc.mm"
include "sbceq1a.mm"
include "biimpac.mm"

theorem pm13.13a
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( ( ph /\ x = A ) -> [. A / x ]. ph )

  proof
    vx
    cv
    cA
    wceq
    wph
    wph
    vx
    cA
    wsbc
    wph
    vx
    cA
    sbceq1a
    biimpac
end

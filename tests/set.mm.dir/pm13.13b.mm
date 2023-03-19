include "cv.mm"
include "wceq.mm"
include "wsbc.mm"
include "sbceq1a.mm"
include "biimparc.mm"

theorem pm13.13b
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( ( [. A / x ]. ph /\ x = A ) -> ph )

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
    biimparc
end

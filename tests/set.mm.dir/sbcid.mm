include "cv.mm"
include "wsbc.mm"
include "wsb.mm"
include "sbsbc.mm"
include "sbid.mm"
include "bitr3i.mm"

theorem sbcid
  let wph: wff ph
  let vx: setvar x


  assert |- ( [. x / x ]. ph <-> ph )

  proof
    wph
    vx
    vx
    cv
    wsbc
    wph
    vx
    vx
    wsb
    wph
    wph
    vx
    vx
    sbsbc
    wph
    vx
    sbid
    bitr3i
end

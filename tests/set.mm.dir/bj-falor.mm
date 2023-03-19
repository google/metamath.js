include "wfal.mm"
include "fal.mm"
include "bj-biorfi.mm"

theorem bj-falor
  let wph: wff ph


  assert |- ( ph <-> ( F. \/ ph ) )

  proof
    wfal
    wph
    fal
    bj-biorfi
end

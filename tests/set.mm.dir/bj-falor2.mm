include "wfal.mm"
include "wo.mm"
include "falim.mm"
include "bj-jaoi1.mm"
include "olc.mm"
include "impbii.mm"

theorem bj-falor2
  let wph: wff ph


  assert |- ( ( F. \/ ph ) <-> ph )

  proof
    wfal
    wph
    wo
    wph
    wfal
    wph
    wph
    falim
    bj-jaoi1
    wph
    wfal
    olc
    impbii
end

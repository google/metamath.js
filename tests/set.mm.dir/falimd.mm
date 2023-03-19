include "wfal.mm"
include "falim.mm"
include "adantl.mm"

theorem falimd
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph /\ F. ) -> ps )

  proof
    wfal
    wps
    wph
    wps
    falim
    adantl
end

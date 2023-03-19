include "wo.mm"
include "wfal.mm"
include "orc.mm"
include "falim.mm"
include "orim2i.mm"
include "jaoi.mm"

theorem dissym1
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ps \/ ( ps \/ F. ) ) -> ( ps \/ ph ) )

  proof
    wps
    wps
    wph
    wo
    wps
    wfal
    wo
    wps
    wph
    orc
    wfal
    wph
    wps
    wph
    falim
    orim2i
    jaoi
end

include "wfal.mm"
include "falim.mm"
include "jaoi.mm"

theorem orfa1
  let wph: wff ph
  let wps: wff ps
  assume orfa1.1: |- ( ph -> ps )


  assert |- ( ( ph \/ F. ) -> ps )

  proof
    wph
    wps
    wfal
    orfa1.1
    wps
    falim
    jaoi
end

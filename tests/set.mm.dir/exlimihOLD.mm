include "nfiOLD.mm"
include "exlimiOLD.mm"

theorem exlimihOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume exlimihOLD.1: |- ( ps -> A. x ps )
  assume exlimihOLD.2: |- ( ph -> ps )


  assert |- ( E. x ph -> ps )

  proof
    wph
    wps
    vx
    wps
    vx
    exlimihOLD.1
    nfiOLD
    exlimihOLD.2
    exlimiOLD
end

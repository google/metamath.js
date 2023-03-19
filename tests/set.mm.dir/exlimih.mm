include "nf5i.mm"
include "exlimi.mm"

theorem exlimih
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume exlimih.1: |- ( ps -> A. x ps )
  assume exlimih.2: |- ( ph -> ps )


  assert |- ( E. x ph -> ps )

  proof
    wph
    wps
    vx
    wps
    vx
    exlimih.1
    nf5i
    exlimih.2
    exlimi
end

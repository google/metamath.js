include "ex.mm"
include "pm2.43i.mm"

theorem anidms
  let wph: wff ph
  let wps: wff ps
  assume anidms.1: |- ( ( ph /\ ph ) -> ps )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wph
    wph
    wps
    anidms.1
    ex
    pm2.43i
end

include "wn.mm"
include "ex.mm"
include "pm2.01d.mm"

theorem pm2.01da
  let wph: wff ph
  let wps: wff ps
  assume pm2.01da.1: |- ( ( ph /\ ps ) -> -. ps )


  assert |- ( ph -> -. ps )

  proof
    wph
    wps
    wph
    wps
    wps
    wn
    pm2.01da.1
    ex
    pm2.01d
end

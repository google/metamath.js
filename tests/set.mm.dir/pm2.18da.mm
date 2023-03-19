include "wn.mm"
include "ex.mm"
include "pm2.18d.mm"

theorem pm2.18da
  let wph: wff ph
  let wps: wff ps
  assume pm2.18da.1: |- ( ( ph /\ -. ps ) -> ps )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wph
    wps
    wn
    wps
    pm2.18da.1
    ex
    pm2.18d
end

include "ex.mm"
include "wn.mm"
include "pm2.65d.mm"

theorem pm2.65da
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume pm2.65da.1: |- ( ( ph /\ ps ) -> ch )
  assume pm2.65da.2: |- ( ( ph /\ ps ) -> -. ch )


  assert |- ( ph -> -. ps )

  proof
    wph
    wps
    wch
    wph
    wps
    wch
    pm2.65da.1
    ex
    wph
    wps
    wch
    wn
    pm2.65da.2
    ex
    pm2.65d
end

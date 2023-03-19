include "ex.mm"
include "wn.mm"
include "pm2.61d.mm"

theorem pm2.61dan
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume pm2.61dan.1: |- ( ( ph /\ ps ) -> ch )
  assume pm2.61dan.2: |- ( ( ph /\ -. ps ) -> ch )


  assert |- ( ph -> ch )

  proof
    wph
    wps
    wch
    wph
    wps
    wch
    pm2.61dan.1
    ex
    wph
    wps
    wn
    wch
    pm2.61dan.2
    ex
    pm2.61d
end

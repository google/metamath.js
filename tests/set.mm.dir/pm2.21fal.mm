include "wfal.mm"
include "pm2.21dd.mm"

theorem pm2.21fal
  let wph: wff ph
  let wps: wff ps
  assume pm2.21fal.1: |- ( ph -> ps )
  assume pm2.21fal.2: |- ( ph -> -. ps )


  assert |- ( ph -> F. )

  proof
    wph
    wps
    wfal
    pm2.21fal.1
    pm2.21fal.2
    pm2.21dd
end

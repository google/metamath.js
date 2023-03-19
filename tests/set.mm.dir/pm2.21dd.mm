include "pm2.65i.mm"
include "pm2.21i.mm"

theorem pm2.21dd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume pm2.21dd.1: |- ( ph -> ps )
  assume pm2.21dd.2: |- ( ph -> -. ps )


  assert |- ( ph -> ch )

  proof
    wph
    wch
    wph
    wps
    pm2.21dd.1
    pm2.21dd.2
    pm2.65i
    pm2.21i
end

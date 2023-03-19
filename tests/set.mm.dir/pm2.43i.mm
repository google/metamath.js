include "id.mm"
include "mpd.mm"

theorem pm2.43i
  let wph: wff ph
  let wps: wff ps
  assume pm2.43i.1: |- ( ph -> ( ph -> ps ) )


  assert |- ( ph -> ps )

  proof
    wph
    wph
    wps
    wph
    id
    pm2.43i.1
    mpd
end

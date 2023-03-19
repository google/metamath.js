include "pm2.43a.mm"
include "com12.mm"

theorem pm2.43b
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume pm2.43b.1: |- ( ps -> ( ph -> ( ps -> ch ) ) )


  assert |- ( ph -> ( ps -> ch ) )

  proof
    wps
    wph
    wch
    wph
    wps
    wch
    pm2.43b.1
    pm2.43a
    com12
end

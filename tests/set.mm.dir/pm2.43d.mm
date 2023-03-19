include "id.mm"
include "mpdi.mm"

theorem pm2.43d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume pm2.43d.1: |- ( ph -> ( ps -> ( ps -> ch ) ) )


  assert |- ( ph -> ( ps -> ch ) )

  proof
    wph
    wps
    wps
    wch
    wps
    id
    pm2.43d.1
    mpdi
end

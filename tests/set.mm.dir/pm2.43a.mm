include "id.mm"
include "mpid.mm"

theorem pm2.43a
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume pm2.43a.1: |- ( ps -> ( ph -> ( ps -> ch ) ) )


  assert |- ( ps -> ( ph -> ch ) )

  proof
    wps
    wph
    wps
    wch
    wps
    id
    pm2.43a.1
    mpid
end

include "nsyld.mm"
include "pm2.01d.mm"

theorem pm2.65d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume pm2.65d.1: |- ( ph -> ( ps -> ch ) )
  assume pm2.65d.2: |- ( ph -> ( ps -> -. ch ) )


  assert |- ( ph -> -. ps )

  proof
    wph
    wps
    wph
    wps
    wch
    wps
    pm2.65d.2
    pm2.65d.1
    nsyld
    pm2.01d
end

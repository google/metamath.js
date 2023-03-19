include "wn.mm"
include "id.mm"
include "pm2.61d1.mm"

theorem pm2.01d
  let wph: wff ph
  let wps: wff ps
  assume pm2.01d.1: |- ( ph -> ( ps -> -. ps ) )


  assert |- ( ph -> -. ps )

  proof
    wph
    wps
    wps
    wn
    #
    pm2.01d.1
    @0
    id
    pm2.61d1
end

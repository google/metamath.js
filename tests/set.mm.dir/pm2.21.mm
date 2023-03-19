include "wn.mm"
include "id.mm"
include "pm2.21d.mm"

theorem pm2.21
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ph -> ( ph -> ps ) )

  proof
    wph
    wn
    #
    wph
    wps
    @0
    id
    pm2.21d
end

include "wn.mm"
include "wi.mm"
include "pm2.21.mm"
include "id.mm"
include "jaoi.mm"

theorem pm2.42
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( -. ph \/ ( ph -> ps ) ) -> ( ph -> ps ) )

  proof
    wph
    wn
    wph
    wps
    wi
    #
    @0
    wph
    wps
    pm2.21
    @0
    id
    jaoi
end

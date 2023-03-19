include "wi.mm"
include "id.mm"
include "com12.mm"

theorem pm2.27
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph -> ( ( ph -> ps ) -> ps ) )

  proof
    wph
    wps
    wi
    #
    wph
    wps
    @0
    id
    com12
end

include "wi.mm"
include "id.mm"
include "com23.mm"

theorem pm2.04
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch


  assert |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) )

  proof
    wph
    wps
    wch
    wi
    wi
    #
    wph
    wps
    wch
    @0
    id
    com23
end

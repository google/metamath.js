include "wi.mm"
include "id.mm"
include "com23.mm"

theorem pm2.04
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


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

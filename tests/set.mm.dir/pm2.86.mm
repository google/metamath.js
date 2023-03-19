include "wi.mm"
include "id.mm"
include "pm2.86d.mm"

theorem pm2.86
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph -> ps ) -> ( ph -> ch ) ) -> ( ph -> ( ps -> ch ) ) )

  proof
    wph
    wps
    wi
    wph
    wch
    wi
    wi
    #
    wph
    wps
    wch
    @0
    id
    pm2.86d
end

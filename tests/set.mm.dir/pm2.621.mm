include "wi.mm"
include "id.mm"
include "idd.mm"
include "jaod.mm"

theorem pm2.621
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ps ) -> ( ( ph \/ ps ) -> ps ) )

  proof
    wph
    wps
    wi
    #
    wph
    wps
    wps
    @0
    id
    @0
    wps
    idd
    jaod
end

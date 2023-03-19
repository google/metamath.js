include "wi.mm"
include "id.mm"
include "orim1d.mm"

theorem pm2.38
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ps -> ch ) -> ( ( ps \/ ph ) -> ( ch \/ ph ) ) )

  proof
    wps
    wch
    wi
    #
    wps
    wch
    wph
    @0
    id
    orim1d
end

include "wi.mm"
include "id.mm"
include "orim2d.mm"

theorem orim2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ps -> ch ) -> ( ( ph \/ ps ) -> ( ph \/ ch ) ) )

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
    orim2d
end

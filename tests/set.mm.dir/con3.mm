include "wi.mm"
include "id.mm"
include "con3d.mm"

theorem con3
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) )

  proof
    wph
    wps
    wi
    #
    wph
    wps
    @0
    id
    con3d
end

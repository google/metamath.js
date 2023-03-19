include "wn.mm"
include "wi.mm"
include "id.mm"
include "con2d.mm"

theorem con2
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> -. ps ) -> ( ps -> -. ph ) )

  proof
    wph
    wps
    wn
    wi
    #
    wph
    wps
    @0
    id
    con2d
end

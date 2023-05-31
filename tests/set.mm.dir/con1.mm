include "wn.mm"
include "wi.mm"
include "id.mm"
include "con1d.mm"

theorem con1
  param wph: wff ph
  param wps: wff ps


  assert |- ( ( -. ph -> ps ) -> ( -. ps -> ph ) )

  proof
    wph
    wn
    wps
    wi
    #
    wph
    wps
    @0
    id
    con1d
end

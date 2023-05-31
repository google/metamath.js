include "wi.mm"
include "id.mm"
include "a1i.mm"

theorem idd
  param wph: wff ph
  param wps: wff ps


  assert |- ( ph -> ( ps -> ps ) )

  proof
    wps
    wps
    wi
    wph
    wps
    id
    a1i
end

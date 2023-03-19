include "wi.mm"
include "id.mm"
include "a1i.mm"

theorem idd
  let wph: wff ph
  let wps: wff ps


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

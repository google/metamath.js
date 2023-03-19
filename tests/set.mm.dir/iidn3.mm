include "wi.mm"
include "id.mm"
include "2a1i.mm"

theorem iidn3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ph -> ( ps -> ( ch -> ch ) ) )

  proof
    wch
    wch
    wi
    wph
    wps
    wch
    id
    2a1i
end

include "wi.mm"
include "a1dd.mm"

theorem 2a1dd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 2a1dd.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( ps -> ( th -> ( ta -> ch ) ) ) )

  proof
    wph
    wps
    wta
    wch
    wi
    wth
    wph
    wps
    wch
    wta
    2a1dd.1
    a1dd
    a1dd
end

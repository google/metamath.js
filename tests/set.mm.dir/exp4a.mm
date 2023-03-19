include "wa.mm"
include "wi.mm"
include "imp.mm"
include "exp4b.mm"

theorem exp4a
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume exp4a.1: |- ( ph -> ( ps -> ( ( ch /\ th ) -> ta ) ) )


  assert |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wph
    wps
    wch
    wth
    wa
    wta
    wi
    exp4a.1
    imp
    exp4b
end

include "wa.mm"
include "exp32.mm"
include "exp4a.mm"

theorem exp45
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume exp45.1: |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> ta )


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
    exp45.1
    exp32
    exp4a
end

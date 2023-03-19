include "wa.mm"
include "ex.mm"
include "exp4b.mm"

theorem exp43
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume exp43.1: |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta )


  assert |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wph
    wps
    wa
    wch
    wth
    wa
    wta
    exp43.1
    ex
    exp4b
end

include "wa.mm"
include "expd.mm"
include "exp4a.mm"

theorem exp4d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume exp4d.1: |- ( ph -> ( ( ps /\ ( ch /\ th ) ) -> ta ) )


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
    exp4d.1
    expd
    exp4a
end

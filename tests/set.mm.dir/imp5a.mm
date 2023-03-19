include "wi.mm"
include "wa.mm"
include "pm3.31.mm"
include "syl8.mm"

theorem imp5a
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume imp5.1: |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) )


  assert |- ( ph -> ( ps -> ( ch -> ( ( th /\ ta ) -> et ) ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    wi
    wi
    wth
    wta
    wa
    wet
    wi
    imp5.1
    wth
    wta
    wet
    pm3.31
    syl8
end

include "wa.mm"
include "wi.mm"
include "imp31.mm"
include "impd.mm"

theorem imp5d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume imp5.1: |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) )


  assert |- ( ( ( ph /\ ps ) /\ ch ) -> ( ( th /\ ta ) -> et ) )

  proof
    wph
    wps
    wa
    wch
    wa
    wth
    wta
    wet
    wph
    wps
    wch
    wth
    wta
    wet
    wi
    wi
    imp5.1
    imp31
    impd
end

include "wa.mm"
include "wi.mm"
include "impd.mm"

theorem imp4c
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume imp4.1: |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )


  assert |- ( ph -> ( ( ( ps /\ ch ) /\ th ) -> ta ) )

  proof
    wph
    wps
    wch
    wa
    wth
    wta
    wph
    wps
    wch
    wth
    wta
    wi
    imp4.1
    impd
    impd
end

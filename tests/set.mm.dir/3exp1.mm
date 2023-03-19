include "wi.mm"
include "w3a.mm"
include "ex.mm"
include "3exp.mm"

theorem 3exp1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3exp1.1: |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta )


  assert |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wi
    wph
    wps
    wch
    w3a
    wth
    wta
    3exp1.1
    ex
    3exp
end

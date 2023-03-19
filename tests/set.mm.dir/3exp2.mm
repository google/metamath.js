include "w3a.mm"
include "ex.mm"
include "3expd.mm"

theorem 3exp2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3exp2.1: |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta )


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
    w3a
    wta
    3exp2.1
    ex
    3expd
end

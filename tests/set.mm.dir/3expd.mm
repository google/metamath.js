include "wi.mm"
include "w3a.mm"
include "com12.mm"
include "3exp.mm"
include "com4r.mm"

theorem 3expd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3expd.1: |- ( ph -> ( ( ps /\ ch /\ th ) -> ta ) )


  assert |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )

  proof
    wps
    wch
    wth
    wph
    wta
    wps
    wch
    wth
    wph
    wta
    wi
    wph
    wps
    wch
    wth
    w3a
    wta
    3expd.1
    com12
    3exp
    com4r
end

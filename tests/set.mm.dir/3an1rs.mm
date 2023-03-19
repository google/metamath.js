include "w3a.mm"
include "wi.mm"
include "ex.mm"
include "3exp.mm"
include "com34.mm"
include "3imp.mm"
include "imp.mm"

theorem 3an1rs
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3an1rs.1: |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta )


  assert |- ( ( ( ph /\ ps /\ th ) /\ ch ) -> ta )

  proof
    wph
    wps
    wth
    w3a
    wch
    wta
    wph
    wps
    wth
    wch
    wta
    wi
    wph
    wps
    wch
    wth
    wta
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
    3an1rs.1
    ex
    3exp
    com34
    3imp
    imp
end

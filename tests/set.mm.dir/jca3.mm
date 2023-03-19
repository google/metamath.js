include "wa.mm"
include "wi.mm"
include "imp.mm"
include "a1d.mm"
include "jca2.mm"
include "ex.mm"

theorem jca3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume jca3.1: |- ( ph -> ( ps -> ch ) )
  assume jca3.2: |- ( th -> ta )


  assert |- ( ph -> ( ps -> ( th -> ( ch /\ ta ) ) ) )

  proof
    wph
    wps
    wth
    wch
    wta
    wa
    wi
    wph
    wps
    wa
    #
    wth
    wch
    wta
    @0
    wch
    wth
    wph
    wps
    wch
    jca3.1
    imp
    a1d
    jca3.2
    jca2
    ex
end

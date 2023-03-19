include "wa.mm"
include "wi.mm"
include "ex.mm"
include "2a1dd.mm"
include "a1ddd.mm"
include "com45.mm"
include "com23.mm"
include "com34.mm"
include "imp.mm"
include "imp41.mm"

theorem ad5ant14
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ad5ant14.1: |- ( ( ph /\ ps ) -> ch )


  assert |- ( ( ( ( ( ph /\ th ) /\ ta ) /\ ps ) /\ et ) -> ch )

  proof
    wph
    wth
    wa
    wta
    wps
    wet
    wch
    wph
    wth
    wta
    wps
    wet
    wch
    wi
    #
    wi
    wi
    wph
    wth
    wps
    wta
    @0
    wph
    wps
    wth
    wta
    @0
    wi
    wph
    wps
    wth
    wet
    wta
    wch
    wph
    wps
    wth
    wet
    wta
    wch
    wi
    wph
    wps
    wch
    wth
    wta
    wph
    wps
    wch
    ad5ant14.1
    ex
    2a1dd
    a1ddd
    com45
    com23
    com34
    imp
    imp41
end

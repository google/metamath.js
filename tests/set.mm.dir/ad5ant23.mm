include "wa.mm"
include "wi.mm"
include "ex.mm"
include "2a1dd.mm"
include "a1ddd.mm"
include "com45.mm"
include "com3r.mm"
include "imp.mm"
include "imp41.mm"

theorem ad5ant23
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ad5ant23.1: |- ( ( ph /\ ps ) -> ch )


  assert |- ( ( ( ( ( th /\ ph ) /\ ps ) /\ ta ) /\ et ) -> ch )

  proof
    wth
    wph
    wa
    wps
    wta
    wet
    wch
    wth
    wph
    wps
    wta
    wet
    wch
    wi
    wi
    #
    wi
    wph
    wps
    wth
    @0
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
    ad5ant23.1
    ex
    2a1dd
    a1ddd
    com45
    com3r
    imp
    imp41
end

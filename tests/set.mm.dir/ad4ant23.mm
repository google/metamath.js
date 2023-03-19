include "wi.mm"
include "ex.mm"
include "a1dd.mm"
include "a1i.mm"
include "imp41.mm"

theorem ad4ant23
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume ad4ant23.1: |- ( ( ph /\ ps ) -> ch )


  assert |- ( ( ( ( th /\ ph ) /\ ps ) /\ ta ) -> ch )

  proof
    wth
    wph
    wps
    wta
    wch
    wph
    wps
    wta
    wch
    wi
    wi
    wi
    wth
    wph
    wps
    wch
    wta
    wph
    wps
    wch
    ad4ant23.1
    ex
    a1dd
    a1i
    imp41
end

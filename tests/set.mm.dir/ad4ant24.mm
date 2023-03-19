include "wi.mm"
include "ex.mm"
include "a1i13.mm"
include "imp41.mm"

theorem ad4ant24
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume ad4ant24.1: |- ( ( ph /\ ps ) -> ch )


  assert |- ( ( ( ( th /\ ph ) /\ ta ) /\ ps ) -> ch )

  proof
    wth
    wph
    wta
    wps
    wch
    wth
    wph
    wta
    wps
    wch
    wi
    wph
    wps
    wch
    ad4ant24.1
    ex
    a1i13
    imp41
end

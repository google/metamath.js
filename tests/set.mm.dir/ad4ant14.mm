include "wi.mm"
include "ex.mm"
include "2a1d.mm"
include "imp41.mm"

theorem ad4ant14
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume ad4ant14.1: |- ( ( ph /\ ps ) -> ch )


  assert |- ( ( ( ( ph /\ th ) /\ ta ) /\ ps ) -> ch )

  proof
    wph
    wth
    wta
    wps
    wch
    wph
    wps
    wch
    wi
    wth
    wta
    wph
    wps
    wch
    ad4ant14.1
    ex
    2a1d
    imp41
end

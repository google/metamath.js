include "wi.mm"
include "ex.mm"
include "a1dd.mm"
include "a1d.mm"
include "imp41.mm"

theorem ad4ant13
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume ad4ant13.1: |- ( ( ph /\ ps ) -> ch )


  assert |- ( ( ( ( ph /\ th ) /\ ps ) /\ ta ) -> ch )

  proof
    wph
    wth
    wps
    wta
    wch
    wph
    wps
    wta
    wch
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
    ad4ant13.1
    ex
    a1dd
    a1d
    imp41
end

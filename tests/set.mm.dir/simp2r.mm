include "wa.mm"
include "simpr.mm"
include "3ad2ant2.mm"

theorem simp2r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ( ps /\ ch ) /\ th ) -> ch )

  proof
    wps
    wch
    wa
    wph
    wch
    wth
    wps
    wch
    simpr
    3ad2ant2
end

include "wa.mm"
include "simpr.mm"
include "sylan2.mm"

theorem adantrl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume adant2.1: |- ( ( ph /\ ps ) -> ch )


  assert |- ( ( ph /\ ( th /\ ps ) ) -> ch )

  proof
    wth
    wps
    wa
    wph
    wps
    wch
    wth
    wps
    simpr
    adant2.1
    sylan2
end

include "wa.mm"
include "simpr.mm"
include "sylan.mm"

theorem adantll
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume adant2.1: |- ( ( ph /\ ps ) -> ch )


  assert |- ( ( ( th /\ ph ) /\ ps ) -> ch )

  proof
    wth
    wph
    wa
    wph
    wps
    wch
    wth
    wph
    simpr
    adant2.1
    sylan
end

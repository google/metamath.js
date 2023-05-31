include "wa.mm"
include "simpr.mm"
include "sylan.mm"

theorem adantll
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
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

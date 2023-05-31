include "wa.mm"
include "simpr.mm"
include "syl5.mm"

theorem adantld
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume adantld.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( ( th /\ ps ) -> ch ) )

  proof
    wth
    wps
    wa
    wps
    wph
    wch
    wth
    wps
    simpr
    adantld.1
    syl5
end

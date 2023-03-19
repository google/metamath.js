include "wa.mm"
include "simpr.mm"
include "syl5.mm"

theorem adantld
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
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

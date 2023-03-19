include "wa.mm"
include "simpr.mm"
include "wb.mm"
include "ad4ant123.mm"
include "mpbird.mm"

theorem 4animp1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 4animp1.1: |- ( ( ph /\ ps /\ ch ) -> ( ta <-> th ) )


  assert |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta )

  proof
    wph
    wps
    wa
    wch
    wa
    #
    wth
    wa
    wta
    wth
    @0
    wth
    simpr
    wph
    wps
    wch
    wta
    wth
    wb
    wth
    4animp1.1
    ad4ant123
    mpbird
end

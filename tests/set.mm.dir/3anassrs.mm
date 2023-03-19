include "3exp2.mm"
include "imp41.mm"

theorem 3anassrs
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3anassrs.1: |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta )


  assert |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta )

  proof
    wph
    wps
    wch
    wth
    wta
    wph
    wps
    wch
    wth
    wta
    3anassrs.1
    3exp2
    imp41
end

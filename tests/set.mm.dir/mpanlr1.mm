include "wa.mm"
include "jctl.mm"
include "sylanl2.mm"

theorem mpanlr1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume mpanlr1.1: |- ps
  assume mpanlr1.2: |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ta )


  assert |- ( ( ( ph /\ ch ) /\ th ) -> ta )

  proof
    wch
    wph
    wps
    wch
    wa
    wth
    wta
    wch
    wps
    mpanlr1.1
    jctl
    mpanlr1.2
    sylanl2
end

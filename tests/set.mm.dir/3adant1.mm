include "w3a.mm"
include "wa.mm"
include "3simpc.mm"
include "syl.mm"

theorem 3adant1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3adant.1: |- ( ( ph /\ ps ) -> ch )


  assert |- ( ( th /\ ph /\ ps ) -> ch )

  proof
    wth
    wph
    wps
    w3a
    wph
    wps
    wa
    wch
    wth
    wph
    wps
    3simpc
    3adant.1
    syl
end

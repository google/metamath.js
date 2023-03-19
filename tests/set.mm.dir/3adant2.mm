include "w3a.mm"
include "wa.mm"
include "3simpb.mm"
include "syl.mm"

theorem 3adant2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3adant.1: |- ( ( ph /\ ps ) -> ch )


  assert |- ( ( ph /\ th /\ ps ) -> ch )

  proof
    wph
    wth
    wps
    w3a
    wph
    wps
    wa
    wch
    wph
    wth
    wps
    3simpb
    3adant.1
    syl
end

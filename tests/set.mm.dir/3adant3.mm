include "w3a.mm"
include "wa.mm"
include "3simpa.mm"
include "syl.mm"

theorem 3adant3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3adant.1: |- ( ( ph /\ ps ) -> ch )


  assert |- ( ( ph /\ ps /\ th ) -> ch )

  proof
    wph
    wps
    wth
    w3a
    wph
    wps
    wa
    wch
    wph
    wps
    wth
    3simpa
    3adant.1
    syl
end

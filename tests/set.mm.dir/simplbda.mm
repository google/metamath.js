include "wa.mm"
include "biimpa.mm"
include "simprd.mm"

theorem simplbda
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume pm3.26bda.1: |- ( ph -> ( ps <-> ( ch /\ th ) ) )


  assert |- ( ( ph /\ ps ) -> th )

  proof
    wph
    wps
    wa
    wch
    wth
    wph
    wps
    wch
    wth
    wa
    pm3.26bda.1
    biimpa
    simprd
end

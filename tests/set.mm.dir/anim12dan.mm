include "wa.mm"
include "ex.mm"
include "anim12d.mm"
include "imp.mm"

theorem anim12dan
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume anim12dan.1: |- ( ( ph /\ ps ) -> ch )
  assume anim12dan.2: |- ( ( ph /\ th ) -> ta )


  assert |- ( ( ph /\ ( ps /\ th ) ) -> ( ch /\ ta ) )

  proof
    wph
    wps
    wth
    wa
    wch
    wta
    wa
    wph
    wps
    wch
    wth
    wta
    wph
    wps
    wch
    anim12dan.1
    ex
    wph
    wth
    wta
    anim12dan.2
    ex
    anim12d
    imp
end

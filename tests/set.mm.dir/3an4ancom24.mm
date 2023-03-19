include "wa.mm"
include "w3a.mm"
include "an4com24.mm"
include "3an4anass.mm"
include "3bitr4i.mm"

theorem 3an4ancom24
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( ( ph /\ ps /\ ch ) /\ th ) <-> ( ( ph /\ th /\ ch ) /\ ps ) )

  proof
    wph
    wps
    wa
    wch
    wth
    wa
    wa
    wph
    wth
    wa
    wch
    wps
    wa
    wa
    wph
    wps
    wch
    w3a
    wth
    wa
    wph
    wth
    wch
    w3a
    wps
    wa
    wph
    wps
    wch
    wth
    an4com24
    wph
    wps
    wch
    wth
    3an4anass
    wph
    wth
    wch
    wps
    3an4anass
    3bitr4i
end

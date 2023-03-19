include "adantll.mm"
include "3adantl1.mm"

theorem 3ad2antl3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3ad2antl.1: |- ( ( ph /\ ch ) -> th )


  assert |- ( ( ( ps /\ ta /\ ph ) /\ ch ) -> th )

  proof
    wta
    wph
    wch
    wth
    wps
    wph
    wch
    wth
    wta
    3ad2antl.1
    adantll
    3adantl1
end

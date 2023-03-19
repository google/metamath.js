include "adantlr.mm"
include "3adantl1.mm"

theorem 3ad2antl2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3ad2antl.1: |- ( ( ph /\ ch ) -> th )


  assert |- ( ( ( ps /\ ph /\ ta ) /\ ch ) -> th )

  proof
    wph
    wta
    wch
    wth
    wps
    wph
    wch
    wth
    wta
    3ad2antl.1
    adantlr
    3adantl1
end

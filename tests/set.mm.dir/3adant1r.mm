include "wa.mm"
include "3expb.mm"
include "adantlr.mm"
include "3impb.mm"

theorem 3adant1r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3adant1l.1: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ( ( ph /\ ta ) /\ ps /\ ch ) -> th )

  proof
    wph
    wta
    wa
    wps
    wch
    wth
    wph
    wps
    wch
    wa
    wth
    wta
    wph
    wps
    wch
    wth
    3adant1l.1
    3expb
    adantlr
    3impb
end

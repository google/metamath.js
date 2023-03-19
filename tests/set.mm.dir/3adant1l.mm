include "wa.mm"
include "3expb.mm"
include "adantll.mm"
include "3impb.mm"

theorem 3adant1l
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3adant1l.1: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ( ( ta /\ ph ) /\ ps /\ ch ) -> th )

  proof
    wta
    wph
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
    adantll
    3impb
end

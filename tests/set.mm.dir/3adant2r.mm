include "wa.mm"
include "3com12.mm"
include "3adant1r.mm"

theorem 3adant2r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3adant1l.1: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ( ph /\ ( ps /\ ta ) /\ ch ) -> th )

  proof
    wps
    wta
    wa
    wph
    wch
    wth
    wps
    wph
    wch
    wth
    wta
    wph
    wps
    wch
    wth
    3adant1l.1
    3com12
    3adant1r
    3com12
end

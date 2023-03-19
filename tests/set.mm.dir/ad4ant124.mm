include "wi.mm"
include "3exp.mm"
include "a1dd.mm"
include "imp41.mm"

theorem ad4ant124
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume ad4ant124.1: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ( ( ( ph /\ ps ) /\ ta ) /\ ch ) -> th )

  proof
    wph
    wps
    wta
    wch
    wth
    wph
    wps
    wch
    wth
    wi
    wta
    wph
    wps
    wch
    wth
    ad4ant124.1
    3exp
    a1dd
    imp41
end

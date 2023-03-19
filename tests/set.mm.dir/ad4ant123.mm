include "3exp.mm"
include "a1ddd.mm"
include "imp41.mm"

theorem ad4ant123
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume ad4ant123.1: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ( ( ( ph /\ ps ) /\ ch ) /\ ta ) -> th )

  proof
    wph
    wps
    wch
    wta
    wth
    wph
    wps
    wch
    wta
    wth
    wph
    wps
    wch
    wth
    ad4ant123.1
    3exp
    a1ddd
    imp41
end

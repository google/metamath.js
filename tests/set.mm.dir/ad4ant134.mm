include "wi.mm"
include "3exp.mm"
include "a1d.mm"
include "imp41.mm"

theorem ad4ant134
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume ad4ant134.1: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ( ( ( ph /\ ta ) /\ ps ) /\ ch ) -> th )

  proof
    wph
    wta
    wps
    wch
    wth
    wph
    wps
    wch
    wth
    wi
    wi
    wta
    wph
    wps
    wch
    wth
    ad4ant134.1
    3exp
    a1d
    imp41
end

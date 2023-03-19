include "wi.mm"
include "3exp.mm"
include "a1i.mm"
include "imp41.mm"

theorem ad4ant234
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume ad4ant234.1: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ( ( ( ta /\ ph ) /\ ps ) /\ ch ) -> th )

  proof
    wta
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    wth
    wi
    wi
    wi
    wta
    wph
    wps
    wch
    wth
    ad4ant234.1
    3exp
    a1i
    imp41
end

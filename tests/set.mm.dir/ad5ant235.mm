include "wa.mm"
include "wi.mm"
include "3exp.mm"
include "a1ddd.mm"
include "com5r.mm"
include "com45.mm"
include "imp.mm"
include "imp41.mm"

theorem ad5ant235
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ad5ant235.1: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ( ( ( ( ta /\ ph ) /\ ps ) /\ et ) /\ ch ) -> th )

  proof
    wta
    wph
    wa
    wps
    wet
    wch
    wth
    wta
    wph
    wps
    wet
    wch
    wth
    wi
    wi
    wi
    wta
    wph
    wps
    wch
    wet
    wth
    wph
    wps
    wch
    wet
    wta
    wth
    wph
    wps
    wch
    wet
    wta
    wth
    wi
    wph
    wps
    wch
    wta
    wth
    wph
    wps
    wch
    wth
    ad5ant235.1
    3exp
    a1ddd
    a1ddd
    com5r
    com45
    imp
    imp41
end

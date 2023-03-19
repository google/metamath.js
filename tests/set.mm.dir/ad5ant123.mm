include "wa.mm"
include "wi.mm"
include "3exp.mm"
include "a1ddd.mm"
include "com45.mm"
include "imp.mm"
include "imp41.mm"

theorem ad5ant123
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ad5ant123.1: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ( ( ( ( ph /\ ps ) /\ ch ) /\ ta ) /\ et ) -> th )

  proof
    wph
    wps
    wa
    wch
    wta
    wet
    wth
    wph
    wps
    wch
    wta
    wet
    wth
    wi
    wi
    wi
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
    ad5ant123.1
    3exp
    a1ddd
    a1ddd
    com45
    imp
    imp41
end

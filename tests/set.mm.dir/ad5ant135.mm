include "wa.mm"
include "wi.mm"
include "3exp.mm"
include "a1ddd.mm"
include "com45.mm"
include "com34.mm"
include "com23.mm"
include "imp.mm"
include "imp41.mm"

theorem ad5ant135
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ad5ant135.1: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ( ( ( ( ph /\ ta ) /\ ps ) /\ et ) /\ ch ) -> th )

  proof
    wph
    wta
    wa
    wps
    wet
    wch
    wth
    wph
    wta
    wps
    wet
    wch
    wth
    wi
    wi
    wi
    wph
    wta
    wps
    wch
    wet
    wth
    wph
    wps
    wta
    wch
    wet
    wth
    wi
    #
    wi
    wph
    wps
    wch
    wta
    @0
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
    ad5ant135.1
    3exp
    a1ddd
    a1ddd
    com45
    com34
    com23
    com45
    imp
    imp41
end

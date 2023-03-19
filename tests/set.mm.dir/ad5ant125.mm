include "wa.mm"
include "wi.mm"
include "3exp.mm"
include "2a1dd.mm"
include "imp.mm"
include "imp41.mm"

theorem ad5ant125
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ad5ant125.1: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ( ( ( ( ph /\ ps ) /\ ta ) /\ et ) /\ ch ) -> th )

  proof
    wph
    wps
    wa
    wta
    wet
    wch
    wth
    wph
    wps
    wta
    wet
    wch
    wth
    wi
    #
    wi
    wi
    wph
    wps
    @0
    wta
    wet
    wph
    wps
    wch
    wth
    ad5ant125.1
    3exp
    2a1dd
    imp
    imp41
end

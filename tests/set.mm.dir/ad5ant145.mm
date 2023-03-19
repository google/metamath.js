include "wa.mm"
include "wi.mm"
include "3exp.mm"
include "2a1d.mm"
include "imp.mm"
include "imp41.mm"

theorem ad5ant145
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ad5ant145.1: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ( ( ( ( ph /\ ta ) /\ et ) /\ ps ) /\ ch ) -> th )

  proof
    wph
    wta
    wa
    wet
    wps
    wch
    wth
    wph
    wta
    wet
    wps
    wch
    wth
    wi
    wi
    #
    wi
    wph
    @0
    wta
    wet
    wph
    wps
    wch
    wth
    ad5ant145.1
    3exp
    2a1d
    imp
    imp41
end

include "wa.mm"
include "wi.mm"
include "3exp.mm"
include "a1i13.mm"
include "imp.mm"
include "imp41.mm"

theorem ad5ant245
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ad5ant245.1: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ( ( ( ( ta /\ ph ) /\ et ) /\ ps ) /\ ch ) -> th )

  proof
    wta
    wph
    wa
    wet
    wps
    wch
    wth
    wta
    wph
    wet
    wps
    wch
    wth
    wi
    wi
    #
    wi
    wta
    wph
    wet
    @0
    wph
    wps
    wch
    wth
    ad5ant245.1
    3exp
    a1i13
    imp
    imp41
end

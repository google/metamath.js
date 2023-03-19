include "wa.mm"
include "w3a.mm"
include "biantrurd.mm"
include "3anass.mm"
include "syl6bbr.mm"

theorem 3biant1d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3biantd.1: |- ( ph -> th )


  assert |- ( ph -> ( ( ch /\ ps ) <-> ( th /\ ch /\ ps ) ) )

  proof
    wph
    wch
    wps
    wa
    #
    wth
    @0
    wa
    wth
    wch
    wps
    w3a
    wph
    wth
    @0
    3biantd.1
    biantrurd
    wth
    wch
    wps
    3anass
    syl6bbr
end

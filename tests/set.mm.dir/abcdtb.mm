include "wa.mm"
include "simpli.mm"
include "simpri.mm"

theorem abcdtb
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vk: setvar k
  let vx: setvar x
  assume abcdtb.1: |- ( ( ( ph /\ ps ) /\ ch ) /\ th )


  assert |- ps

  proof
    wph
    wps
    wph
    wps
    wa
    #
    wch
    @0
    wch
    wa
    wth
    abcdtb.1
    simpli
    simpli
    simpri
end

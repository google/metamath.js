include "wa.mm"
include "simpli.mm"
include "simpri.mm"

theorem abcdtc
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vk: setvar k
  let vx: setvar x
  assume abcdtc.1: |- ( ( ( ph /\ ps ) /\ ch ) /\ th )


  assert |- ch

  proof
    wph
    wps
    wa
    #
    wch
    @0
    wch
    wa
    wth
    abcdtc.1
    simpli
    simpri
end

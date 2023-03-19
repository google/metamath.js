include "wa.mm"
include "simpli.mm"

theorem abcdta
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vk: setvar k
  let vx: setvar x
  assume abcdta.1: |- ( ( ( ph /\ ps ) /\ ch ) /\ th )


  assert |- ph

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
    abcdta.1
    simpli
    simpli
    simpli
end

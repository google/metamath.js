include "wa.mm"
include "simpri.mm"

theorem abcdtd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vk: setvar k
  let vx: setvar x
  assume abcdtd.1: |- ( ( ( ph /\ ps ) /\ ch ) /\ th )


  assert |- th

  proof
    wph
    wps
    wa
    wch
    wa
    wth
    abcdtd.1
    simpri
end

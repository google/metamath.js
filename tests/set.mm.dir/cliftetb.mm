include "wa.mm"
include "wn.mm"
include "wo.mm"
include "2th.mm"

theorem cliftetb
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vk: setvar k
  let vx: setvar x
  assume cliftetb.1: |- ( ( ph /\ ch ) \/ ( ps /\ -. ch ) )
  assume cliftetb.2: |- th


  assert |- ( th <-> ( ( ph /\ ch ) \/ ( ps /\ -. ch ) ) )

  proof
    wth
    wph
    wch
    wa
    wps
    wch
    wn
    wa
    wo
    cliftetb.2
    cliftetb.1
    2th
end

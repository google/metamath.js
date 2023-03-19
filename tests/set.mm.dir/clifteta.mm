include "wn.mm"
include "wa.mm"
include "wo.mm"
include "2th.mm"

theorem clifteta
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vk: setvar k
  let vx: setvar x
  assume clifteta.1: |- ( ( ph /\ -. ch ) \/ ( ps /\ ch ) )
  assume clifteta.2: |- th


  assert |- ( th <-> ( ( ph /\ -. ch ) \/ ( ps /\ ch ) ) )

  proof
    wth
    wph
    wch
    wn
    wa
    wps
    wch
    wa
    wo
    clifteta.2
    clifteta.1
    2th
end

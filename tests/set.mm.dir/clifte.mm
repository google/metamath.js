include "wn.mm"
include "wa.mm"
include "wo.mm"
include "orci.mm"
include "2th.mm"

theorem clifte
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vk: setvar k
  let vx: setvar x
  assume clifte.1: |- ( ph /\ -. ch )
  assume clifte.2: |- th


  assert |- ( th <-> ( ( ph /\ -. ch ) \/ ( ps /\ ch ) ) )

  proof
    wth
    wph
    wch
    wn
    wa
    #
    wps
    wch
    wa
    #
    wo
    clifte.2
    @0
    @1
    clifte.1
    orci
    2th
end

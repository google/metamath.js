include "wa.mm"
include "wn.mm"
include "wo.mm"
include "orci.mm"
include "2th.mm"

theorem cliftet
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vk: setvar k
  let vx: setvar x
  assume cliftet.1: |- ( ph /\ ch )
  assume cliftet.2: |- th


  assert |- ( th <-> ( ( ph /\ ch ) \/ ( ps /\ -. ch ) ) )

  proof
    wth
    wph
    wch
    wa
    #
    wps
    wch
    wn
    wa
    #
    wo
    cliftet.2
    @0
    @1
    cliftet.1
    orci
    2th
end

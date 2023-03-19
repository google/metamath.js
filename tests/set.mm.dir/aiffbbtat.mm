include "wtru.mm"
include "bitri.mm"

theorem aiffbbtat
  let wph: wff ph
  let wps: wff ps
  let vk: setvar k
  let vx: setvar x
  assume aiffbbtat.1: |- ( ph <-> ps )
  assume aiffbbtat.2: |- ( ps <-> T. )


  assert |- ( ph <-> T. )

  proof
    wph
    wps
    wtru
    aiffbbtat.1
    aiffbbtat.2
    bitri
end

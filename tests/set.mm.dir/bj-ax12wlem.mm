include "ax-5.mm"
include "bj-ax12i.mm"

theorem bj-ax12wlem
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume bj-ax12wlem.1: |- ( ph -> ( ps <-> ch ) )

  disjoint ch x
  assert |- ( ph -> ( ps -> A. x ( ph -> ps ) ) )

  proof
    wph
    wps
    wch
    vx
    bj-ax12wlem.1
    wch
    vx
    ax-5
    bj-ax12i
end

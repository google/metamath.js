include "ax-5.mm"
include "ax12i.mm"

theorem ax12wlem
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume ax12wlemw.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint ps x
  assert |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) )

  proof
    wph
    wps
    vx
    vy
    ax12wlemw.1
    wps
    vx
    ax-5
    ax12i
end

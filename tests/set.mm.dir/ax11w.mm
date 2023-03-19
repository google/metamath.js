include "alcomiw.mm"

theorem ax11w
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ax11w.1: |- ( y = z -> ( ph <-> ps ) )

  disjoint y z
  disjoint x y
  disjoint ph z
  disjoint ps y
  assert |- ( A. x A. y ph -> A. y A. x ph )

  proof
    wph
    wps
    vx
    vy
    vz
    ax11w.1
    alcomiw
end

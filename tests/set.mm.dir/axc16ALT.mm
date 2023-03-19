include "wsb.mm"
include "sbequ12.mm"
include "ax-5.mm"
include "hbsb3.mm"
include "axc16i.mm"

theorem axc16ALT
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ph z
  assert |- ( A. x x = y -> ( ph -> A. x ph ) )

  proof
    wph
    wph
    vx
    vz
    wsb
    vx
    vy
    vz
    wph
    vx
    vz
    sbequ12
    wph
    vx
    vz
    wph
    vz
    ax-5
    hbsb3
    axc16i
end

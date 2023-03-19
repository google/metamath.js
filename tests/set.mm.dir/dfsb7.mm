include "nfv.mm"
include "sb7f.mm"

theorem dfsb7
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint y z
  disjoint ph z
  assert |- ( [ y / x ] ph <-> E. z ( z = y /\ E. x ( x = z /\ ph ) ) )

  proof
    wph
    vx
    vy
    vz
    wph
    vz
    nfv
    sb7f
end

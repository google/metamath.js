include "nf5i.mm"
include "sb7f.mm"

theorem sb7h
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume sb7h.1: |- ( ph -> A. z ph )

  disjoint y z
  assert |- ( [ y / x ] ph <-> E. z ( z = y /\ E. x ( x = z /\ ph ) ) )

  proof
    wph
    vx
    vy
    vz
    wph
    vz
    sb7h.1
    nf5i
    sb7f
end

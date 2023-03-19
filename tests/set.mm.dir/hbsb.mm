include "wsb.mm"
include "nf5i.mm"
include "nfsb.mm"
include "nf5ri.mm"

theorem hbsb
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume hbsb.1: |- ( ph -> A. z ph )

  disjoint y z
  assert |- ( [ y / x ] ph -> A. z [ y / x ] ph )

  proof
    wph
    vx
    vy
    wsb
    vz
    wph
    vx
    vy
    vz
    wph
    vz
    hbsb.1
    nf5i
    nfsb
    nf5ri
end

include "wmo.mm"
include "wal.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "gen2.mm"
include "mosubopt.mm"
include "ax-mp.mm"

theorem mosubop
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  assume mosubop.1: |- E* x ph

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- E* x E. y E. z ( A = <. y , z >. /\ ph )

  proof
    wph
    vx
    wmo
    #
    vz
    wal
    vy
    wal
    cA
    vy
    cv
    vz
    cv
    cop
    wceq
    wph
    wa
    vz
    wex
    vy
    wex
    vx
    wmo
    @0
    vy
    vz
    mosubop.1
    gen2
    wph
    vx
    vy
    vz
    cA
    mosubopt
    ax-mp
end

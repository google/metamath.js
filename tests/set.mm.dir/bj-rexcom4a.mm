include "wa.mm"
include "wrex.mm"
include "wex.mm"
include "bj-rexcom4.mm"
include "19.42v.mm"
include "rexbii.mm"
include "bitr3i.mm"

theorem bj-rexcom4a
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint A x
  disjoint x y
  disjoint ph x
  assert |- ( E. x E. y e. A ( ph /\ ps ) <-> E. y e. A ( ph /\ E. x ps ) )

  proof
    wph
    wps
    wa
    #
    vy
    cA
    wrex
    vx
    wex
    @0
    vx
    wex
    #
    vy
    cA
    wrex
    wph
    wps
    vx
    wex
    wa
    #
    vy
    cA
    wrex
    @0
    vy
    vx
    cA
    bj-rexcom4
    @1
    @2
    vy
    cA
    wph
    wps
    vx
    19.42v
    rexbii
    bitr3i
end

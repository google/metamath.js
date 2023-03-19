include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "wex.mm"
include "bj-rexcom4a.mm"
include "bj-isseti.mm"
include "biantru.mm"
include "rexbii.mm"
include "bitr4i.mm"

theorem bj-rexcom4b
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  assume bj-rexcom4b.1: |- B e. V

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint ph x
  assert |- ( E. x E. y e. A ( ph /\ x = B ) <-> E. y e. A ph )

  proof
    wph
    vx
    cv
    cB
    wceq
    #
    wa
    vy
    cA
    wrex
    vx
    wex
    wph
    @0
    vx
    wex
    #
    wa
    #
    vy
    cA
    wrex
    wph
    vy
    cA
    wrex
    wph
    @0
    vx
    vy
    cA
    bj-rexcom4a
    wph
    @2
    vy
    cA
    @1
    wph
    vx
    cB
    cV
    bj-rexcom4b.1
    bj-isseti
    biantru
    rexbii
    bitr4i
end

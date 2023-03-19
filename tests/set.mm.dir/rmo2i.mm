include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "wex.mm"
include "wrmo.mm"
include "rexex.mm"
include "rmo2.mm"
include "sylibr.mm"

theorem rmo2i
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume rmo2.1: |- F/ y ph

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( E. y e. A A. x e. A ( ph -> x = y ) -> E* x e. A ph )

  proof
    wph
    vx
    vy
    weq
    wi
    vx
    cA
    wral
    #
    vy
    cA
    wrex
    @0
    vy
    wex
    wph
    vx
    cA
    wrmo
    @0
    vy
    cA
    rexex
    wph
    vx
    vy
    cA
    rmo2.1
    rmo2
    sylibr
end

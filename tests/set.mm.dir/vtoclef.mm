include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "isseti.mm"
include "exlimi.mm"
include "ax-mp.mm"

theorem vtoclef
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume vtoclef.1: |- F/ x ph
  assume vtoclef.2: |- A e. _V
  assume vtoclef.3: |- ( x = A -> ph )

  disjoint A x
  assert |- ph

  proof
    vx
    cv
    cA
    wceq
    #
    vx
    wex
    wph
    vx
    cA
    vtoclef.2
    isseti
    @0
    wph
    vx
    vtoclef.1
    vtoclef.3
    exlimi
    ax-mp
end

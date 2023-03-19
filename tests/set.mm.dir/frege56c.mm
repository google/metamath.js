include "wceq.mm"
include "wi.mm"
include "wsbc.mm"
include "cv.mm"
include "frege54cor1c.mm"
include "frege53c.mm"
include "ax-mp.mm"
include "frege55lem1c.mm"
include "frege9.mm"

theorem frege56c
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume frege56c.b: |- B e. C

  disjoint A x
  disjoint B x
  assert |- ( ( A = B -> ( [. A / x ]. ph -> [. B / x ]. ph ) ) -> ( B = A -> ( [. A / x ]. ph -> [. B / x ]. ph ) ) )

  proof
    cB
    cA
    wceq
    #
    cA
    cB
    wceq
    #
    wi
    #
    @1
    wph
    vx
    cA
    wsbc
    wph
    vx
    cB
    wsbc
    wi
    #
    wi
    @0
    @3
    wi
    wi
    @0
    vx
    cv
    cB
    wceq
    #
    vx
    cA
    wsbc
    wi
    #
    @2
    @4
    vx
    cB
    wsbc
    @5
    vx
    cB
    cC
    frege56c.b
    frege54cor1c
    @4
    vx
    cB
    cA
    frege53c
    ax-mp
    @0
    vx
    cA
    cB
    frege55lem1c
    ax-mp
    @0
    @1
    @3
    frege9
    ax-mp
end

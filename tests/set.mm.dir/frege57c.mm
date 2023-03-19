include "wceq.mm"
include "wsbc.mm"
include "wi.mm"
include "ax-frege52c.mm"
include "frege56c.mm"
include "ax-mp.mm"

theorem frege57c
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume frege57c.a: |- A e. C

  disjoint A x
  disjoint B x
  assert |- ( A = B -> ( [. B / x ]. ph -> [. A / x ]. ph ) )

  proof
    cB
    cA
    wceq
    wph
    vx
    cB
    wsbc
    wph
    vx
    cA
    wsbc
    wi
    #
    wi
    cA
    cB
    wceq
    @0
    wi
    wph
    vx
    cB
    cA
    ax-frege52c
    wph
    vx
    cB
    cA
    cC
    frege57c.a
    frege56c
    ax-mp
end

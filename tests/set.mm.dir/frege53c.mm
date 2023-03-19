include "wceq.mm"
include "wsbc.mm"
include "wi.mm"
include "ax-frege52c.mm"
include "ax-frege8.mm"
include "ax-mp.mm"

theorem frege53c
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B


  assert |- ( [. A / x ]. ph -> ( A = B -> [. B / x ]. ph ) )

  proof
    cA
    cB
    wceq
    #
    wph
    vx
    cA
    wsbc
    #
    wph
    vx
    cB
    wsbc
    #
    wi
    wi
    @1
    @0
    @2
    wi
    wi
    wph
    vx
    cA
    cB
    ax-frege52c
    @0
    @1
    @2
    ax-frege8
    ax-mp
end

include "wceq.mm"
include "cab.mm"
include "wcel.mm"
include "wsbc.mm"
include "eleq1.mm"
include "df-sbc.mm"
include "3bitr4g.mm"

theorem dfsbcq
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B


  assert |- ( A = B -> ( [. A / x ]. ph <-> [. B / x ]. ph ) )

  proof
    cA
    cB
    wceq
    cA
    wph
    vx
    cab
    #
    wcel
    cB
    @0
    wcel
    wph
    vx
    cA
    wsbc
    wph
    vx
    cB
    wsbc
    cA
    cB
    @0
    eleq1
    wph
    vx
    cA
    df-sbc
    wph
    vx
    cB
    df-sbc
    3bitr4g
end

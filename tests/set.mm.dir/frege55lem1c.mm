include "cv.mm"
include "wceq.mm"
include "wsbc.mm"
include "cab.mm"
include "wcel.mm"
include "df-sbc.mm"
include "eqeq1.mm"
include "elabg.mm"
include "ibi.mm"
include "sylbi.mm"
include "imim2i.mm"

theorem frege55lem1c
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( ph -> [. A / x ]. x = B ) -> ( ph -> A = B ) )

  proof
    vx
    cv
    #
    cB
    wceq
    #
    vx
    cA
    wsbc
    #
    cA
    cB
    wceq
    #
    wph
    @2
    cA
    @1
    vx
    cab
    #
    wcel
    #
    @3
    @1
    vx
    cA
    df-sbc
    @5
    @3
    @1
    @3
    vx
    cA
    @4
    @0
    cA
    cB
    eqeq1
    elabg
    ibi
    sylbi
    imim2i
end

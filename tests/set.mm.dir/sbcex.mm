include "wsbc.mm"
include "cab.mm"
include "wcel.mm"
include "cvv.mm"
include "df-sbc.mm"
include "elex.mm"
include "sylbi.mm"

theorem sbcex
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( [. A / x ]. ph -> A e. _V )

  proof
    wph
    vx
    cA
    wsbc
    cA
    wph
    vx
    cab
    #
    wcel
    cA
    cvv
    wcel
    wph
    vx
    cA
    df-sbc
    cA
    @0
    elex
    sylbi
end

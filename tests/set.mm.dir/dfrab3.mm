include "crab.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "cin.mm"
include "df-rab.mm"
include "inab.mm"
include "abid2.mm"
include "ineq1i.mm"
include "3eqtr2i.mm"

theorem dfrab3
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- { x e. A | ph } = ( A i^i { x | ph } )

  proof
    wph
    vx
    cA
    crab
    vx
    cv
    cA
    wcel
    #
    wph
    wa
    vx
    cab
    @0
    vx
    cab
    #
    wph
    vx
    cab
    #
    cin
    cA
    @2
    cin
    wph
    vx
    cA
    df-rab
    @0
    wph
    vx
    inab
    @1
    cA
    @2
    vx
    cA
    abid2
    ineq1i
    3eqtr2i
end

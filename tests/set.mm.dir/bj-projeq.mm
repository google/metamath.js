include "wceq.mm"
include "bj-cproj.mm"
include "wa.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "wcel.mm"
include "cab.mm"
include "simpr.mm"
include "simpl.mm"
include "sneqd.mm"
include "imaeq12d.mm"
include "eleq2d.mm"
include "abbidv.mm"
include "df-bj-proj.mm"
include "3eqtr4g.mm"
include "ex.mm"

theorem bj-projeq
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x


  assert |- ( A = C -> ( B = D -> ( A Proj B ) = ( C Proj D ) ) )

  proof
    cA
    cC
    wceq
    #
    cB
    cD
    wceq
    #
    cA
    cB
    bj-cproj
    #
    cC
    cD
    bj-cproj
    #
    wceq
    @0
    @1
    wa
    #
    vx
    cv
    csn
    #
    cB
    cA
    csn
    #
    cima
    #
    wcel
    #
    vx
    cab
    @5
    cD
    cC
    csn
    #
    cima
    #
    wcel
    #
    vx
    cab
    @2
    @3
    @4
    @8
    @11
    vx
    @4
    @7
    @10
    @5
    @4
    cB
    cD
    @6
    @9
    @0
    @1
    simpr
    @4
    cA
    cC
    @0
    @1
    simpl
    sneqd
    imaeq12d
    eleq2d
    abbidv
    vx
    cA
    cB
    df-bj-proj
    vx
    cC
    cD
    df-bj-proj
    3eqtr4g
    ex
end

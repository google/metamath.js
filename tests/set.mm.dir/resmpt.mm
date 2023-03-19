include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "cres.mm"
include "cmpt.mm"
include "resopab2.mm"
include "df-mpt.mm"
include "reseq1i.mm"
include "3eqtr4g.mm"

theorem resmpt
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  assert |- ( B C_ A -> ( ( x e. A |-> C ) |` B ) = ( x e. B |-> C ) )

  proof
    cB
    cA
    wss
    vx
    cv
    #
    cA
    wcel
    vy
    cv
    cC
    wceq
    #
    wa
    vx
    vy
    copab
    #
    cB
    cres
    @0
    cB
    wcel
    @1
    wa
    vx
    vy
    copab
    vx
    cA
    cC
    cmpt
    #
    cB
    cres
    vx
    cB
    cC
    cmpt
    @1
    vx
    vy
    cB
    cA
    resopab2
    @3
    @2
    cB
    vx
    vy
    cA
    cC
    df-mpt
    reseq1i
    vx
    vy
    cB
    cC
    df-mpt
    3eqtr4g
end

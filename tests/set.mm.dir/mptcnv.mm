include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "cmpt.mm"
include "ccnv.mm"
include "opabbidv.mm"
include "df-mpt.mm"
include "cnveqi.mm"
include "cnvopab.mm"
include "eqtri.mm"
include "3eqtr4g.mm"

theorem mptcnv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume mptcnv.1: |- ( ph -> ( ( x e. A /\ y = B ) <-> ( y e. C /\ x = D ) ) )

  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint C x
  disjoint D x
  disjoint A y
  disjoint B y
  assert |- ( ph -> `' ( x e. A |-> B ) = ( y e. C |-> D ) )

  proof
    wph
    vx
    cv
    #
    cA
    wcel
    vy
    cv
    #
    cB
    wceq
    wa
    #
    vy
    vx
    copab
    #
    @1
    cC
    wcel
    @0
    cD
    wceq
    wa
    #
    vy
    vx
    copab
    vx
    cA
    cB
    cmpt
    #
    ccnv
    #
    vy
    cC
    cD
    cmpt
    wph
    @2
    @4
    vy
    vx
    mptcnv.1
    opabbidv
    @6
    @2
    vx
    vy
    copab
    #
    ccnv
    @3
    @5
    @7
    vx
    vy
    cA
    cB
    df-mpt
    cnveqi
    @2
    vx
    vy
    cnvopab
    eqtri
    vy
    vx
    cC
    cD
    df-mpt
    3eqtr4g
end

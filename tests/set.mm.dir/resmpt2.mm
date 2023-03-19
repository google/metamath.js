include "wss.mm"
include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "coprab.mm"
include "cxp.mm"
include "cres.mm"
include "cmpt2.mm"
include "resoprab2.mm"
include "df-mpt2.mm"
include "reseq1i.mm"
include "3eqtr4g.mm"

theorem resmpt2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let vz: setvar z

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint A z
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint C z
  disjoint D z
  disjoint E z
  assert |- ( ( C C_ A /\ D C_ B ) -> ( ( x e. A , y e. B |-> E ) |` ( C X. D ) ) = ( x e. C , y e. D |-> E ) )

  proof
    cC
    cA
    wss
    cD
    cB
    wss
    wa
    vx
    cv
    #
    cA
    wcel
    vy
    cv
    #
    cB
    wcel
    wa
    vz
    cv
    cE
    wceq
    #
    wa
    vx
    vy
    vz
    coprab
    #
    cC
    cD
    cxp
    #
    cres
    @0
    cC
    wcel
    @1
    cD
    wcel
    wa
    @2
    wa
    vx
    vy
    vz
    coprab
    vx
    vy
    cA
    cB
    cE
    cmpt2
    #
    @4
    cres
    vx
    vy
    cC
    cD
    cE
    cmpt2
    @2
    vx
    vy
    vz
    cA
    cB
    cC
    cD
    resoprab2
    @5
    @3
    @4
    vx
    vy
    vz
    cA
    cB
    cE
    df-mpt2
    reseq1i
    vx
    vy
    vz
    cC
    cD
    cE
    df-mpt2
    3eqtr4g
end

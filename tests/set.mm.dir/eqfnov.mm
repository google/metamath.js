include "cxp.mm"
include "wfn.mm"
include "wa.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "co.mm"
include "eqfnfv2.mm"
include "cop.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "df-ov.mm"
include "eqeq12i.mm"
include "syl6bbr.mm"
include "ralxp.mm"
include "anbi2i.mm"
include "syl6bb.mm"

theorem eqfnov
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint D z
  disjoint F z
  disjoint G z
  assert |- ( ( F Fn ( A X. B ) /\ G Fn ( C X. D ) ) -> ( F = G <-> ( ( A X. B ) = ( C X. D ) /\ A. x e. A A. y e. B ( x F y ) = ( x G y ) ) ) )

  proof
    cF
    cA
    cB
    cxp
    #
    wfn
    cG
    cC
    cD
    cxp
    #
    wfn
    wa
    cF
    cG
    wceq
    @0
    @1
    wceq
    #
    vz
    cv
    #
    cF
    cfv
    #
    @3
    cG
    cfv
    #
    wceq
    #
    vz
    @0
    wral
    #
    wa
    @2
    vx
    cv
    #
    vy
    cv
    #
    cF
    co
    #
    @8
    @9
    cG
    co
    #
    wceq
    #
    vy
    cB
    wral
    vx
    cA
    wral
    #
    wa
    vz
    @0
    @1
    cF
    cG
    eqfnfv2
    @7
    @13
    @2
    @6
    @12
    vz
    vx
    vy
    cA
    cB
    @3
    @8
    @9
    cop
    #
    wceq
    #
    @6
    @14
    cF
    cfv
    #
    @14
    cG
    cfv
    #
    wceq
    @12
    @15
    @4
    @16
    @5
    @17
    @3
    @14
    cF
    fveq2
    @3
    @14
    cG
    fveq2
    eqeq12d
    @10
    @16
    @11
    @17
    @8
    @9
    cF
    df-ov
    @8
    @9
    cG
    df-ov
    eqeq12i
    syl6bbr
    ralxp
    anbi2i
    syl6bb
end

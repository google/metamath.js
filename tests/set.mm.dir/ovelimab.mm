include "wfn.mm"
include "cxp.mm"
include "wss.mm"
include "wa.mm"
include "cima.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "co.mm"
include "fvelimab.mm"
include "cop.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "eqeq1d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "rexxp.mm"

theorem ovelimab
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint F x
  disjoint F y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint D z
  disjoint F z
  assert |- ( ( F Fn A /\ ( B X. C ) C_ A ) -> ( D e. ( F " ( B X. C ) ) <-> E. x e. B E. y e. C D = ( x F y ) ) )

  proof
    cF
    cA
    wfn
    cB
    cC
    cxp
    #
    cA
    wss
    wa
    cD
    cF
    @0
    cima
    wcel
    vz
    cv
    #
    cF
    cfv
    #
    cD
    wceq
    #
    vz
    @0
    wrex
    cD
    vx
    cv
    #
    vy
    cv
    #
    cF
    co
    #
    wceq
    #
    vy
    cC
    wrex
    vx
    cB
    wrex
    vz
    cA
    @0
    cD
    cF
    fvelimab
    @3
    @7
    vz
    vx
    vy
    cB
    cC
    @1
    @4
    @5
    cop
    #
    wceq
    #
    @3
    @6
    cD
    wceq
    @7
    @9
    @2
    @6
    cD
    @9
    @2
    @8
    cF
    cfv
    @6
    @1
    @8
    cF
    fveq2
    @4
    @5
    cF
    df-ov
    syl6eqr
    eqeq1d
    @6
    cD
    eqcom
    syl6bb
    rexxp
    syl6bb
end

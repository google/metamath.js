include "cxp.mm"
include "wfo.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "co.mm"
include "dffo3.mm"
include "cop.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "eqeq2d.mm"
include "rexxp.mm"
include "ralbii.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem foov
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B w
  disjoint C w
  disjoint F w
  assert |- ( F : ( A X. B ) -onto-> C <-> ( F : ( A X. B ) --> C /\ A. z e. C E. x e. A E. y e. B z = ( x F y ) ) )

  proof
    cA
    cB
    cxp
    #
    cC
    cF
    wfo
    @0
    cC
    cF
    wf
    #
    vz
    cv
    #
    vw
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vw
    @0
    wrex
    #
    vz
    cC
    wral
    #
    wa
    @1
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
    wceq
    #
    vy
    cB
    wrex
    vx
    cA
    wrex
    #
    vz
    cC
    wral
    #
    wa
    vw
    vz
    @0
    cC
    cF
    dffo3
    @7
    @13
    @1
    @6
    @12
    vz
    cC
    @5
    @11
    vw
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
    @4
    @10
    @2
    @15
    @4
    @14
    cF
    cfv
    @10
    @3
    @14
    cF
    fveq2
    @8
    @9
    cF
    df-ov
    syl6eqr
    eqeq2d
    rexxp
    ralbii
    anbi2i
    bitri
end

include "wcel.mm"
include "wral.mm"
include "crn.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "rnmpt2.mm"
include "abeq2i.mm"
include "wa.mm"
include "simpl.mm"
include "simpr.mm"
include "r19.29d2r.mm"
include "wi.mm"
include "eleq1.mm"
include "biimparc.mm"
include "a1i.mm"
include "rexlimivv.mm"
include "syl.mm"
include "ex.mm"
include "syl5bi.mm"
include "ssrdv.mm"

theorem rnmpt2ss
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let vz: setvar z
  assume rnmpt2ss.1: |- F = ( x e. A , y e. B |-> C )

  disjoint A y
  disjoint x y
  disjoint D x
  disjoint D y
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint x z
  disjoint D z
  disjoint F z
  assert |- ( A. x e. A A. y e. B C e. D -> ran F C_ D )

  proof
    cC
    cD
    wcel
    #
    vy
    cB
    wral
    vx
    cA
    wral
    #
    vz
    cF
    crn
    #
    cD
    vz
    cv
    #
    @2
    wcel
    @3
    cC
    wceq
    #
    vy
    cB
    wrex
    vx
    cA
    wrex
    #
    @1
    @3
    cD
    wcel
    #
    @5
    vz
    @2
    vx
    vy
    vz
    cA
    cB
    cC
    cF
    rnmpt2ss.1
    rnmpt2
    abeq2i
    @1
    @5
    @6
    @1
    @5
    wa
    #
    @0
    @4
    wa
    #
    vy
    cB
    wrex
    vx
    cA
    wrex
    @6
    @7
    @0
    @4
    vx
    vy
    cA
    cB
    @1
    @5
    simpl
    @1
    @5
    simpr
    r19.29d2r
    @8
    @6
    vx
    vy
    cA
    cB
    @8
    @6
    wi
    vx
    cv
    cA
    wcel
    vy
    cv
    cB
    wcel
    wa
    @4
    @6
    @0
    @3
    cC
    cD
    eleq1
    biimparc
    a1i
    rexlimivv
    syl
    ex
    syl5bi
    ssrdv
end

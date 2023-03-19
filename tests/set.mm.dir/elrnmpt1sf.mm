include "wcel.mm"
include "wceq.mm"
include "wrex.mm"
include "crn.mm"
include "eqid.mm"
include "nfth.mm"
include "cv.mm"
include "eqeq2d.mm"
include "rspce.mm"
include "mpan2.mm"
include "elrnmptf.mm"
include "biimparc.mm"
include "sylan.mm"

theorem elrnmpt1sf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cV: class V
  assume elrnmpt1sf.1: |- F/_ x C
  assume elrnmpt1sf.2: |- F = ( x e. A |-> B )
  assume elrnmpt1sf.3: |- ( x = D -> B = C )

  disjoint A x
  disjoint D x
  assert |- ( ( D e. A /\ C e. V ) -> C e. ran F )

  proof
    cD
    cA
    wcel
    #
    cC
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    cC
    cV
    wcel
    #
    cC
    cF
    crn
    wcel
    #
    @0
    cC
    cC
    wceq
    #
    @2
    cC
    eqid
    #
    @1
    @5
    vx
    cD
    cA
    @5
    vx
    @6
    nfth
    vx
    cv
    cD
    wceq
    cB
    cC
    cC
    elrnmpt1sf.3
    eqeq2d
    rspce
    mpan2
    @3
    @4
    @2
    vx
    cA
    cB
    cC
    cF
    cV
    elrnmpt1sf.1
    elrnmpt1sf.2
    elrnmptf
    biimparc
    sylan
end

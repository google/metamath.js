include "wcel.mm"
include "wceq.mm"
include "wrex.mm"
include "crn.mm"
include "eqid.mm"
include "cv.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpan2.mm"
include "elrnmpt.mm"
include "biimparc.mm"
include "sylan.mm"

theorem elrnmpt1s
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cV: class V
  let vy: setvar y
  let vz: setvar z
  assume rnmpt.1: |- F = ( x e. A |-> B )
  assume elrnmpt1s.1: |- ( x = D -> B = C )

  disjoint A x
  disjoint D x
  disjoint C x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint x y
  disjoint x z
  disjoint C y
  disjoint C z
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
    @1
    @5
    vx
    cD
    cA
    vx
    cv
    cD
    wceq
    cB
    cC
    cC
    elrnmpt1s.1
    eqeq2d
    rspcev
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
    rnmpt.1
    elrnmpt
    biimparc
    sylan
end

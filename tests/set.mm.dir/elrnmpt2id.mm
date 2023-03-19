include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "w3a.mm"
include "cxp.mm"
include "wfn.mm"
include "co.mm"
include "crn.mm"
include "fnmpt2.mm"
include "3ad2ant3.mm"
include "simp1.mm"
include "simp2.mm"
include "fnovrn.mm"
include "syl3anc.mm"

theorem elrnmpt2id
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  assume elrnmpt2id.1: |- F = ( x e. A , y e. B |-> C )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  assert |- ( ( x e. A /\ y e. B /\ A. x e. A A. y e. B C e. V ) -> ( x F y ) e. ran F )

  proof
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    cC
    cV
    wcel
    vy
    cB
    wral
    vx
    cA
    wral
    #
    w3a
    cF
    cA
    cB
    cxp
    wfn
    #
    @1
    @3
    @0
    @2
    cF
    co
    cF
    crn
    wcel
    @4
    @1
    @5
    @3
    vx
    vy
    cA
    cB
    cC
    cF
    cV
    elrnmpt2id.1
    fnmpt2
    3ad2ant3
    @1
    @3
    @4
    simp1
    @1
    @3
    @4
    simp2
    cA
    cB
    @0
    @2
    cF
    fnovrn
    syl3anc
end

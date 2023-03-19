include "cixp.mm"
include "wcel.mm"
include "cvv.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "w3a.mm"
include "ciun.mm"
include "wf.mm"
include "elixp2.mm"
include "wa.mm"
include "ssiun2.mm"
include "sseld.mm"
include "ralimia.mm"
include "anim2i.mm"
include "nfcv.mm"
include "nfiu1.mm"
include "ffnfvf.mm"
include "sylibr.mm"
include "3adant1.mm"
include "sylbi.mm"

theorem ixpf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vf: setvar f
  let cC: class C

  disjoint A x
  disjoint F x
  disjoint f x
  disjoint A f
  disjoint B f
  disjoint C f
  assert |- ( F e. X_ x e. A B -> F : A --> U_ x e. A B )

  proof
    cF
    vx
    cA
    cB
    cixp
    wcel
    cF
    cvv
    wcel
    #
    cF
    cA
    wfn
    #
    vx
    cv
    #
    cF
    cfv
    #
    cB
    wcel
    #
    vx
    cA
    wral
    #
    w3a
    cA
    vx
    cA
    cB
    ciun
    #
    cF
    wf
    #
    vx
    cA
    cB
    cF
    elixp2
    @1
    @5
    @7
    @0
    @1
    @5
    wa
    @1
    @3
    @6
    wcel
    #
    vx
    cA
    wral
    #
    wa
    @7
    @5
    @9
    @1
    @4
    @8
    vx
    cA
    @2
    cA
    wcel
    cB
    @6
    @3
    vx
    cA
    cB
    ssiun2
    sseld
    ralimia
    anim2i
    vx
    cA
    @6
    cF
    vx
    cA
    nfcv
    vx
    cA
    cB
    nfiu1
    vx
    cF
    nfcv
    ffnfvf
    sylibr
    3adant1
    sylbi
end

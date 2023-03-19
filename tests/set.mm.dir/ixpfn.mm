include "cv.mm"
include "wfn.mm"
include "cixp.mm"
include "fneq1.mm"
include "wcel.mm"
include "cvv.mm"
include "cfv.mm"
include "wral.mm"
include "elixp2.mm"
include "simp2bi.mm"
include "vtoclga.mm"

theorem ixpfn
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vf: setvar f

  disjoint A x
  disjoint A f
  disjoint f x
  disjoint B f
  disjoint F f
  assert |- ( F e. X_ x e. A B -> F Fn A )

  proof
    vf
    cv
    #
    cA
    wfn
    #
    cF
    cA
    wfn
    vf
    cF
    vx
    cA
    cB
    cixp
    #
    cA
    @0
    cF
    fneq1
    @0
    @2
    wcel
    @0
    cvv
    wcel
    @1
    vx
    cv
    @0
    cfv
    cB
    wcel
    vx
    cA
    wral
    vx
    cA
    cB
    @0
    elixp2
    simp2bi
    vtoclga
end

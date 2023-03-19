include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "eleq1d.mm"
include "vtoclga.mm"
include "fvmptg.mm"
include "mpdan.mm"

theorem fvmpt3
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cV: class V
  assume fvmpt3.a: |- ( x = A -> B = C )
  assume fvmpt3.b: |- F = ( x e. D |-> B )
  assume fvmpt3.c: |- ( x e. D -> B e. V )

  disjoint A x
  disjoint C x
  disjoint D x
  disjoint V x
  assert |- ( A e. D -> ( F ` A ) = C )

  proof
    cA
    cD
    wcel
    cC
    cV
    wcel
    #
    cA
    cF
    cfv
    cC
    wceq
    cB
    cV
    wcel
    @0
    vx
    cA
    cD
    vx
    cv
    cA
    wceq
    cB
    cC
    cV
    fvmpt3.a
    eleq1d
    fvmpt3.c
    vtoclga
    vx
    cA
    cB
    cC
    cD
    cV
    cF
    fvmpt3.a
    fvmpt3.b
    fvmptg
    mpdan
end

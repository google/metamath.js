include "wcel.mm"
include "cres.mm"
include "cvv.mm"
include "cfv.mm"
include "wceq.mm"
include "resexg.mm"
include "cv.mm"
include "reseq1.mm"
include "fvmptg.mm"
include "mpdan.mm"

theorem fvtresfn
  let vx: setvar x
  let cB: class B
  let cF: class F
  let cV: class V
  let cX: class X
  assume fvtresfn.f: |- F = ( x e. B |-> ( x |` V ) )

  disjoint B x
  disjoint V x
  disjoint X x
  assert |- ( X e. B -> ( F ` X ) = ( X |` V ) )

  proof
    cX
    cB
    wcel
    cX
    cV
    cres
    #
    cvv
    wcel
    cX
    cF
    cfv
    @0
    wceq
    cX
    cV
    cB
    resexg
    vx
    cX
    vx
    cv
    #
    cV
    cres
    @0
    cB
    cvv
    cF
    @1
    cX
    cV
    reseq1
    fvtresfn.f
    fvmptg
    mpdan
end

include "ccat.mm"
include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "cdm.mm"
include "cmpt.mm"
include "cinv.mm"
include "cfv.mm"
include "ccom.mm"
include "ciso.mm"
include "wceq.mm"
include "df-iso.mm"
include "a1i.mm"
include "fveq2.mm"
include "coeq2d.mm"
include "adantl.mm"
include "id.mm"
include "wfun.mm"
include "funmpt.mm"
include "fvexd.mm"
include "cofunexg.mm"
include "sylancr.mm"
include "fvmptd.mm"

theorem isofval
  let vx: setvar x
  let cC: class C
  let vc: setvar c

  disjoint C x
  disjoint C c
  disjoint c x
  assert |- ( C e. Cat -> ( Iso ` C ) = ( ( x e. _V |-> dom x ) o. ( Inv ` C ) ) )

  proof
    cC
    ccat
    wcel
    #
    vc
    cC
    vx
    cvv
    vx
    cv
    cdm
    #
    cmpt
    #
    vc
    cv
    #
    cinv
    cfv
    #
    ccom
    #
    @2
    cC
    cinv
    cfv
    #
    ccom
    #
    ccat
    ciso
    cvv
    ciso
    vc
    ccat
    @5
    cmpt
    wceq
    @0
    vx
    vc
    df-iso
    a1i
    @3
    cC
    wceq
    #
    @5
    @7
    wceq
    @0
    @8
    @4
    @6
    @2
    @3
    cC
    cinv
    fveq2
    coeq2d
    adantl
    @0
    id
    @0
    @2
    wfun
    @6
    cvv
    wcel
    @7
    cvv
    wcel
    vx
    cvv
    @1
    funmpt
    @0
    cC
    cinv
    fvexd
    @2
    @6
    cvv
    cofunexg
    sylancr
    fvmptd
end

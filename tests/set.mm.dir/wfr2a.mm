include "cv.mm"
include "cfv.mm"
include "cpred.mm"
include "cres.mm"
include "wceq.mm"
include "cdm.mm"
include "fveq2.mm"
include "predeq3.mm"
include "reseq2d.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "wfrlem12.mm"
include "vtoclga.mm"

theorem wfr2a
  let cA: class A
  let cR: class R
  let cF: class F
  let cG: class G
  let cX: class X
  let vx: setvar x
  assume wfr2a.1: |- R We A
  assume wfr2a.2: |- R Se A
  assume wfr2a.3: |- F = wrecs ( R , A , G )


  assert |- ( X e. dom F -> ( F ` X ) = ( G ` ( F |` Pred ( R , A , X ) ) ) )

  proof
    vx
    cv
    #
    cF
    cfv
    #
    cF
    cA
    cR
    @0
    cpred
    #
    cres
    #
    cG
    cfv
    #
    wceq
    cX
    cF
    cfv
    #
    cF
    cA
    cR
    cX
    cpred
    #
    cres
    #
    cG
    cfv
    #
    wceq
    vx
    cX
    cF
    cdm
    @0
    cX
    wceq
    #
    @1
    @5
    @4
    @8
    @0
    cX
    cF
    fveq2
    @9
    @3
    @7
    cG
    @9
    @2
    @6
    cF
    cA
    cR
    @0
    cX
    predeq3
    reseq2d
    fveq2d
    eqeq12d
    vx
    cA
    cR
    cF
    cG
    wfr2a.1
    wfr2a.2
    wfr2a.3
    wfrlem12
    vtoclga
end

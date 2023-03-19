include "cusgr.mm"
include "wcel.mm"
include "cvv.mm"
include "cres.mm"
include "cv.mm"
include "cvtx.mm"
include "cfv.mm"
include "wceq.mm"
include "ciedg.mm"
include "wa.mm"
include "wi.mm"
include "vex.mm"
include "a1i.mm"
include "simprl.mm"
include "simprr.mm"
include "simpl.mm"
include "usgrspan.mm"
include "ex.mm"
include "alrimiv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "resex.mm"
include "gropeld.mm"

theorem usgrspanop
  let cA: class A
  let cE: class E
  let cG: class G
  let cV: class V
  let vg: setvar g
  assume uhgrspanop.v: |- V = ( Vtx ` G )
  assume uhgrspanop.e: |- E = ( iEdg ` G )


  assert |- ( G e. USGraph -> <. V , ( E |` A ) >. e. USGraph )

  proof
    cG
    cusgr
    wcel
    #
    cusgr
    cvv
    vg
    cE
    cA
    cres
    #
    cV
    cvv
    @0
    vg
    cv
    #
    cvtx
    cfv
    cV
    wceq
    #
    @2
    ciedg
    cfv
    @1
    wceq
    #
    wa
    #
    @2
    cusgr
    wcel
    #
    wi
    vg
    @0
    @5
    @6
    @0
    @5
    wa
    #
    cA
    @2
    cE
    cG
    cV
    cvv
    uhgrspanop.v
    uhgrspanop.e
    @2
    cvv
    wcel
    @7
    vg
    vex
    a1i
    @0
    @3
    @4
    simprl
    @0
    @3
    @4
    simprr
    @0
    @5
    simpl
    usgrspan
    ex
    alrimiv
    cV
    cvv
    wcel
    @0
    cV
    cG
    cvtx
    cfv
    cvv
    uhgrspanop.v
    cG
    cvtx
    fvex
    eqeltri
    a1i
    @1
    cvv
    wcel
    @0
    cE
    cA
    cE
    cG
    ciedg
    cfv
    cvv
    uhgrspanop.e
    cG
    ciedg
    fvex
    eqeltri
    resex
    a1i
    gropeld
end

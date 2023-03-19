include "cgr.mm"
include "wcel.mm"
include "cghomOLD.mm"
include "co.mm"
include "wf.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "elghomOLD.mm"
include "simprbda.mm"
include "3impa.mm"

theorem ghomf
  let cF: class F
  let cG: class G
  let cH: class H
  let cW: class W
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume ghomf.1: |- X = ran G
  assume ghomf.2: |- W = ran H


  assert |- ( ( G e. GrpOp /\ H e. GrpOp /\ F e. ( G GrpOpHom H ) ) -> F : X --> W )

  proof
    cG
    cgr
    wcel
    #
    cH
    cgr
    wcel
    #
    cF
    cG
    cH
    cghomOLD
    co
    wcel
    #
    cX
    cW
    cF
    wf
    #
    @0
    @1
    wa
    @2
    @3
    vx
    cv
    #
    cF
    cfv
    vy
    cv
    #
    cF
    cfv
    cH
    co
    @4
    @5
    cG
    co
    cF
    cfv
    wceq
    vy
    cX
    wral
    vx
    cX
    wral
    vx
    vy
    cF
    cG
    cH
    cW
    cX
    ghomf.1
    ghomf.2
    elghomOLD
    simprbda
    3impa
end

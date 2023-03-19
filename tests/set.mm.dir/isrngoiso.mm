include "crngo.mm"
include "wcel.mm"
include "wa.mm"
include "crngiso.mm"
include "co.mm"
include "cv.mm"
include "wf1o.mm"
include "crnghom.mm"
include "crab.mm"
include "rngoisoval.mm"
include "eleq2d.mm"
include "f1oeq1.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem isrngoiso
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vr: setvar r
  let vs: setvar s
  assume rngisoval.1: |- G = ( 1st ` R )
  assume rngisoval.2: |- X = ran G
  assume rngisoval.3: |- J = ( 1st ` S )
  assume rngisoval.4: |- Y = ran J


  assert |- ( ( R e. RingOps /\ S e. RingOps ) -> ( F e. ( R RngIso S ) <-> ( F e. ( R RngHom S ) /\ F : X -1-1-onto-> Y ) ) )

  proof
    cR
    crngo
    wcel
    cS
    crngo
    wcel
    wa
    #
    cF
    cR
    cS
    crngiso
    co
    #
    wcel
    cF
    cX
    cY
    vf
    cv
    #
    wf1o
    #
    vf
    cR
    cS
    crnghom
    co
    #
    crab
    #
    wcel
    cF
    @4
    wcel
    cX
    cY
    cF
    wf1o
    #
    wa
    @0
    @1
    @5
    cF
    cR
    cS
    vf
    cG
    cJ
    cX
    cY
    rngisoval.1
    rngisoval.2
    rngisoval.3
    rngisoval.4
    rngoisoval
    eleq2d
    @3
    @6
    vf
    cF
    @4
    cX
    cY
    @2
    cF
    f1oeq1
    elrab
    syl6bb
end

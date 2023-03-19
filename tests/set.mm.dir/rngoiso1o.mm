include "crngo.mm"
include "wcel.mm"
include "crngiso.mm"
include "co.mm"
include "wf1o.mm"
include "wa.mm"
include "crnghom.mm"
include "isrngoiso.mm"
include "simplbda.mm"
include "3impa.mm"

theorem rngoiso1o
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


  assert |- ( ( R e. RingOps /\ S e. RingOps /\ F e. ( R RngIso S ) ) -> F : X -1-1-onto-> Y )

  proof
    cR
    crngo
    wcel
    #
    cS
    crngo
    wcel
    #
    cF
    cR
    cS
    crngiso
    co
    wcel
    #
    cX
    cY
    cF
    wf1o
    #
    @0
    @1
    wa
    @2
    cF
    cR
    cS
    crnghom
    co
    wcel
    @3
    cR
    cS
    cF
    cG
    cJ
    cX
    cY
    rngisoval.1
    rngisoval.2
    rngisoval.3
    rngisoval.4
    isrngoiso
    simplbda
    3impa
end

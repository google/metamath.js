include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "ccfil.mm"
include "cfil.mm"
include "cv.mm"
include "cxp.mm"
include "cima.mm"
include "cc0.mm"
include "cico.mm"
include "co.mm"
include "wss.mm"
include "wrex.mm"
include "crp.mm"
include "wral.mm"
include "iscfil.mm"
include "simprbda.mm"

theorem cfilfil
  let cD: class D
  let cF: class F
  let cX: class X
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let vf: setvar f
  let vr: setvar r
  let cG: class G
  let cJ: class J
  let cR: class R
  let cY: class Y
  let vd: setvar d


  assert |- ( ( D e. ( *Met ` X ) /\ F e. ( CauFil ` D ) ) -> F e. ( Fil ` X ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    cF
    cD
    ccfil
    cfv
    wcel
    cF
    cX
    cfil
    cfv
    wcel
    cD
    vy
    cv
    #
    @0
    cxp
    cima
    cc0
    vx
    cv
    cico
    co
    wss
    vy
    cF
    wrex
    vx
    crp
    wral
    vx
    vy
    cD
    cF
    cX
    iscfil
    simprbda
end

include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "ccfil.mm"
include "wa.mm"
include "cfil.mm"
include "wss.mm"
include "cv.mm"
include "cxp.mm"
include "cima.mm"
include "cc0.mm"
include "cico.mm"
include "co.mm"
include "wrex.mm"
include "crp.mm"
include "wral.mm"
include "simprl.mm"
include "simprr.mm"
include "iscfil.mm"
include "simplbda.mm"
include "adantr.mm"
include "ssrexv.mm"
include "ralimdv.mm"
include "sylc.mm"
include "wb.mm"
include "ad2antrr.mm"
include "mpbir2and.mm"

theorem cfilss
  let cD: class D
  let cF: class F
  let cG: class G
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
  let cJ: class J
  let cR: class R
  let cY: class Y
  let vd: setvar d


  assert |- ( ( ( D e. ( *Met ` X ) /\ F e. ( CauFil ` D ) ) /\ ( G e. ( Fil ` X ) /\ F C_ G ) ) -> G e. ( CauFil ` D ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cF
    cD
    ccfil
    cfv
    #
    wcel
    #
    wa
    #
    cG
    cX
    cfil
    cfv
    #
    wcel
    #
    cF
    cG
    wss
    #
    wa
    #
    wa
    #
    cG
    @1
    wcel
    #
    @5
    cD
    vy
    cv
    #
    @10
    cxp
    cima
    cc0
    vx
    cv
    cico
    co
    wss
    #
    vy
    cG
    wrex
    #
    vx
    crp
    wral
    #
    @3
    @5
    @6
    simprl
    @8
    @6
    @11
    vy
    cF
    wrex
    #
    vx
    crp
    wral
    #
    @13
    @3
    @5
    @6
    simprr
    @3
    @15
    @7
    @0
    @2
    cF
    @4
    wcel
    @15
    vx
    vy
    cD
    cF
    cX
    iscfil
    simplbda
    adantr
    @6
    @14
    @12
    vx
    crp
    @11
    vy
    cF
    cG
    ssrexv
    ralimdv
    sylc
    @0
    @9
    @5
    @13
    wa
    wb
    @2
    @7
    vx
    vy
    cD
    cG
    cX
    iscfil
    ad2antrr
    mpbir2and
end

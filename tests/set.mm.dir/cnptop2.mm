include "ccnp.mm"
include "co.mm"
include "cfv.mm"
include "wcel.mm"
include "ctop.mm"
include "cuni.mm"
include "w3a.mm"
include "wf.mm"
include "cv.mm"
include "cima.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "eqid.mm"
include "iscnp2.mm"
include "simplbi.mm"
include "simp2d.mm"

theorem cnptop2
  let cP: class P
  let cF: class F
  let cJ: class J
  let cK: class K
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  let cY: class Y


  assert |- ( F e. ( ( J CnP K ) ` P ) -> K e. Top )

  proof
    cF
    cP
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    cJ
    ctop
    wcel
    #
    cK
    ctop
    wcel
    #
    cP
    cJ
    cuni
    #
    wcel
    #
    @0
    @1
    @2
    @4
    w3a
    @3
    cK
    cuni
    #
    cF
    wf
    cP
    cF
    cfv
    vy
    cv
    #
    wcel
    cP
    vx
    cv
    #
    wcel
    cF
    @7
    cima
    @6
    wss
    wa
    vx
    cJ
    wrex
    wi
    vy
    cK
    wral
    wa
    vx
    vy
    cP
    cF
    cJ
    cK
    @3
    @5
    @3
    eqid
    @5
    eqid
    iscnp2
    simplbi
    simp2d
end

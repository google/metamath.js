include "ccnp.mm"
include "co.mm"
include "cfv.mm"
include "wcel.mm"
include "ctop.mm"
include "w3a.mm"
include "cuni.mm"
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
include "simp3d.mm"

theorem cnprcl
  let cP: class P
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cY: class Y
  assume iscnp2.1: |- X = U. J


  assert |- ( F e. ( ( J CnP K ) ` P ) -> P e. X )

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
    cX
    wcel
    #
    @0
    @1
    @2
    @3
    w3a
    cX
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
    @6
    cima
    @5
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
    cX
    @4
    iscnp2.1
    @4
    eqid
    iscnp2
    simplbi
    simp3d
end

include "ccnp.mm"
include "co.mm"
include "cfv.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "cima.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "ctop.mm"
include "w3a.mm"
include "iscnp2.mm"
include "simprbi.mm"
include "simpld.mm"

theorem cnpf
  let cP: class P
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume iscnp2.1: |- X = U. J
  assume iscnp2.2: |- Y = U. K


  assert |- ( F e. ( ( J CnP K ) ` P ) -> F : X --> Y )

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
    cX
    cY
    cF
    wf
    #
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
    @3
    cima
    @2
    wss
    wa
    vx
    cJ
    wrex
    wi
    vy
    cK
    wral
    #
    @0
    cJ
    ctop
    wcel
    cK
    ctop
    wcel
    cP
    cX
    wcel
    w3a
    @1
    @4
    wa
    vx
    vy
    cP
    cF
    cJ
    cK
    cX
    cY
    iscnp2.1
    iscnp2.2
    iscnp2
    simprbi
    simpld
end

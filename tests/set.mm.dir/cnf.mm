include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "wral.mm"
include "ctop.mm"
include "wa.mm"
include "iscn2.mm"
include "simprbi.mm"
include "simpld.mm"

theorem cnf
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  assume iscnp2.1: |- X = U. J
  assume iscnp2.2: |- Y = U. K


  assert |- ( F e. ( J Cn K ) -> F : X --> Y )

  proof
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    cX
    cY
    cF
    wf
    #
    cF
    ccnv
    vx
    cv
    cima
    cJ
    wcel
    vx
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
    wa
    @1
    @2
    wa
    vx
    cF
    cJ
    cK
    cX
    cY
    iscnp2.1
    iscnp2.2
    iscn2
    simprbi
    simpld
end

include "wcel.mm"
include "ccn.mm"
include "co.mm"
include "ccnp.mm"
include "cfv.mm"
include "cv.mm"
include "cncnpi.mm"
include "expcom.mm"
include "ssrdv.mm"

theorem cnsscnp
  let cP: class P
  let cJ: class J
  let cK: class K
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let vf: setvar f
  assume cnsscnp.1: |- X = U. J


  assert |- ( P e. X -> ( J Cn K ) C_ ( ( J CnP K ) ` P ) )

  proof
    cP
    cX
    wcel
    #
    vf
    cJ
    cK
    ccn
    co
    #
    cP
    cJ
    cK
    ccnp
    co
    cfv
    #
    vf
    cv
    #
    @1
    wcel
    @0
    @3
    @2
    wcel
    cP
    @3
    cJ
    cK
    cX
    cnsscnp.1
    cncnpi
    expcom
    ssrdv
end

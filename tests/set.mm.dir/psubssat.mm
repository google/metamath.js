include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "cjn.mm"
include "cfv.mm"
include "co.mm"
include "cple.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "eqid.mm"
include "ispsubsp.mm"
include "simprbda.mm"

theorem psubssat
  let cA: class A
  let cB: class B
  let cS: class S
  let cK: class K
  let cX: class X
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  assume atpsub.a: |- A = ( Atoms ` K )
  assume atpsub.s: |- S = ( PSubSp ` K )


  assert |- ( ( K e. B /\ X e. S ) -> X C_ A )

  proof
    cK
    cB
    wcel
    cX
    cS
    wcel
    cX
    cA
    wss
    vr
    cv
    #
    vp
    cv
    vq
    cv
    cK
    cjn
    cfv
    #
    co
    cK
    cple
    cfv
    #
    wbr
    @0
    cX
    wcel
    wi
    vr
    cA
    wral
    vq
    cX
    wral
    vp
    cX
    wral
    cA
    cB
    cS
    @1
    cK
    @2
    cX
    vr
    vq
    vp
    @2
    eqid
    @1
    eqid
    atpsub.a
    atpsub.s
    ispsubsp
    simprbda
end

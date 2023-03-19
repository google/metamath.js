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
include "wa.mm"
include "ssid.mm"
include "ax-1.mm"
include "rgen.mm"
include "rgen2w.mm"
include "pm3.2i.mm"
include "eqid.mm"
include "ispsubsp.mm"
include "mpbiri.mm"

theorem atpsubN
  let cA: class A
  let cS: class S
  let cK: class K
  let cV: class V
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let cX: class X
  assume atpsub.a: |- A = ( Atoms ` K )
  assume atpsub.s: |- S = ( PSubSp ` K )


  assert |- ( K e. V -> A e. S )

  proof
    cK
    cV
    wcel
    cA
    cS
    wcel
    cA
    cA
    wss
    #
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
    #
    @1
    cA
    wcel
    #
    wi
    #
    vr
    cA
    wral
    #
    vq
    cA
    wral
    vp
    cA
    wral
    #
    wa
    @0
    @8
    cA
    ssid
    @7
    vp
    vq
    cA
    cA
    @6
    vr
    cA
    @5
    @4
    ax-1
    rgen
    rgen2w
    pm3.2i
    cA
    cV
    cS
    @2
    cK
    @3
    cA
    vr
    vq
    vp
    @3
    eqid
    @2
    eqid
    atpsub.a
    atpsub.s
    ispsubsp
    mpbiri
end

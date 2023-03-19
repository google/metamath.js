include "cvv.mm"
include "wcel.mm"
include "csiga.mm"
include "cfv.mm"
include "elex.mm"
include "wa.mm"
include "cv.mm"
include "cdif.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cuni.mm"
include "wi.mm"
include "cpw.mm"
include "wss.mm"
include "w3a.mm"
include "issiga.mm"
include "simplbda.mm"
include "simp1d.mm"
include "mpancom.mm"

theorem baselsiga
  let cA: class A
  let cS: class S
  let vo: setvar o
  let vs: setvar s
  let vx: setvar x


  assert |- ( S e. ( sigAlgebra ` A ) -> A e. S )

  proof
    cS
    cvv
    wcel
    #
    cS
    cA
    csiga
    cfv
    #
    wcel
    #
    cA
    cS
    wcel
    #
    cS
    @1
    elex
    @0
    @2
    wa
    @3
    cA
    vx
    cv
    #
    cdif
    cS
    wcel
    vx
    cS
    wral
    #
    @4
    com
    cdom
    wbr
    @4
    cuni
    cS
    wcel
    wi
    vx
    cS
    cpw
    wral
    #
    @0
    @2
    cS
    cA
    cpw
    wss
    @3
    @5
    @6
    w3a
    vx
    cS
    cA
    issiga
    simplbda
    simp1d
    mpancom
end

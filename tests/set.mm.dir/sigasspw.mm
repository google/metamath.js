include "csiga.mm"
include "cfv.mm"
include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "cv.mm"
include "cdif.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cuni.mm"
include "wi.mm"
include "w3a.mm"
include "cvv.mm"
include "wa.mm"
include "elex.mm"
include "issiga.mm"
include "biimpa.mm"
include "mpancom.mm"
include "simpld.mm"

theorem sigasspw
  let cA: class A
  let cS: class S
  let vo: setvar o
  let vs: setvar s
  let vx: setvar x


  assert |- ( S e. ( sigAlgebra ` A ) -> S C_ ~P A )

  proof
    cS
    cA
    csiga
    cfv
    #
    wcel
    #
    cS
    cA
    cpw
    wss
    #
    cA
    cS
    wcel
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
    @3
    com
    cdom
    wbr
    @3
    cuni
    cS
    wcel
    wi
    vx
    cS
    cpw
    wral
    w3a
    #
    cS
    cvv
    wcel
    #
    @1
    @2
    @4
    wa
    #
    cS
    @0
    elex
    @5
    @1
    @6
    vx
    cS
    cA
    issiga
    biimpa
    mpancom
    simpld
end

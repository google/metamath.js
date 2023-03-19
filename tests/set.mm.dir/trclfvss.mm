include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "ccom.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "ctcl.mm"
include "cfv.mm"
include "trclsslem.mm"
include "3ad2ant3.mm"
include "wceq.mm"
include "trclfv.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "3sstr4d.mm"

theorem trclfvss
  let cR: class R
  let cS: class S
  let cV: class V
  let cW: class W
  let vr: setvar r


  assert |- ( ( R e. V /\ S e. W /\ R C_ S ) -> ( t+ ` R ) C_ ( t+ ` S ) )

  proof
    cR
    cV
    wcel
    #
    cS
    cW
    wcel
    #
    cR
    cS
    wss
    #
    w3a
    cR
    vr
    cv
    #
    wss
    @3
    @3
    ccom
    @3
    wss
    #
    wa
    vr
    cab
    cint
    #
    cS
    @3
    wss
    @4
    wa
    vr
    cab
    cint
    #
    cR
    ctcl
    cfv
    #
    cS
    ctcl
    cfv
    #
    @2
    @0
    @5
    @6
    wss
    @1
    cR
    cS
    vr
    trclsslem
    3ad2ant3
    @0
    @1
    @7
    @5
    wceq
    @2
    vr
    cR
    cV
    trclfv
    3ad2ant1
    @1
    @0
    @8
    @6
    wceq
    @2
    vr
    cS
    cW
    trclfv
    3ad2ant2
    3sstr4d
end

include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "ccom.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "ctcl.mm"
include "cfv.mm"
include "ssmin.mm"
include "trclfv.mm"
include "syl5sseqr.mm"

theorem trclfvlb
  let cR: class R
  let cV: class V
  let vr: setvar r


  assert |- ( R e. V -> R C_ ( t+ ` R ) )

  proof
    cR
    cV
    wcel
    cR
    vr
    cv
    #
    wss
    @0
    @0
    ccom
    @0
    wss
    #
    wa
    vr
    cab
    cint
    cR
    cR
    ctcl
    cfv
    @1
    vr
    cR
    ssmin
    vr
    cR
    cV
    trclfv
    syl5sseqr
end

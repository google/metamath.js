include "com.mm"
include "cina.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "ccf.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cpw.mm"
include "csdm.mm"
include "wbr.mm"
include "wral.mm"
include "peano1.mm"
include "ne0ii.mm"
include "cfom.mm"
include "cfn.mm"
include "nnfi.mm"
include "pwfi.mm"
include "sylib.mm"
include "isfinite.mm"
include "rgen.mm"
include "elina.mm"
include "mpbir3an.mm"

theorem omina
  let vx: setvar x


  assert |- _om e. Inacc

  proof
    com
    cina
    wcel
    com
    c0
    wne
    com
    ccf
    cfv
    com
    wceq
    vx
    cv
    #
    cpw
    #
    com
    csdm
    wbr
    #
    vx
    com
    wral
    c0
    com
    peano1
    ne0ii
    cfom
    @2
    vx
    com
    @0
    com
    wcel
    #
    @1
    cfn
    wcel
    #
    @2
    @3
    @0
    cfn
    wcel
    @4
    @0
    nnfi
    @0
    pwfi
    sylib
    @1
    isfinite
    sylib
    rgen
    vx
    com
    elina
    mpbir3an
end

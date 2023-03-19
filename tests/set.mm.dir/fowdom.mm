include "wcel.mm"
include "cvv.mm"
include "wfo.mm"
include "cwdom.mm"
include "wbr.mm"
include "elex.mm"
include "wa.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "wex.mm"
include "wo.mm"
include "foeq1.mm"
include "spcegv.mm"
include "imp.mm"
include "olcd.mm"
include "wb.mm"
include "wf.mm"
include "fof.mm"
include "dmfex.mm"
include "sylan2.mm"
include "brwdom.mm"
include "syl.mm"
include "mpbird.mm"
include "sylan.mm"

theorem fowdom
  let cF: class F
  let cV: class V
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cZ: class Z


  assert |- ( ( F e. V /\ F : Y -onto-> X ) -> X ~<_* Y )

  proof
    cF
    cV
    wcel
    cF
    cvv
    wcel
    #
    cY
    cX
    cF
    wfo
    #
    cX
    cY
    cwdom
    wbr
    #
    cF
    cV
    elex
    @0
    @1
    wa
    #
    @2
    cX
    c0
    wceq
    #
    cY
    cX
    vz
    cv
    #
    wfo
    #
    vz
    wex
    #
    wo
    #
    @3
    @7
    @4
    @0
    @1
    @7
    @6
    @1
    vz
    cF
    cvv
    cY
    cX
    @5
    cF
    foeq1
    spcegv
    imp
    olcd
    @3
    cY
    cvv
    wcel
    #
    @2
    @8
    wb
    @1
    @0
    cY
    cX
    cF
    wf
    @9
    cY
    cX
    cF
    fof
    cY
    cX
    cvv
    cF
    dmfex
    sylan2
    vz
    cvv
    cX
    cY
    brwdom
    syl
    mpbird
    sylan
end

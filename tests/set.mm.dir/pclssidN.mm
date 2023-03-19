include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "cpsubsp.mm"
include "cfv.mm"
include "crab.mm"
include "cint.mm"
include "ssintub.mm"
include "eqid.mm"
include "pclvalN.mm"
include "syl5sseqr.mm"

theorem pclssidN
  let cA: class A
  let cU: class U
  let cK: class K
  let cV: class V
  let cX: class X
  let vy: setvar y
  let cY: class Y
  assume pclss.a: |- A = ( Atoms ` K )
  assume pclss.c: |- U = ( PCl ` K )


  assert |- ( ( K e. V /\ X C_ A ) -> X C_ ( U ` X ) )

  proof
    cK
    cV
    wcel
    cX
    cA
    wss
    wa
    cX
    vy
    cv
    wss
    vy
    cK
    cpsubsp
    cfv
    #
    crab
    cint
    cX
    cX
    cU
    cfv
    vy
    cX
    @0
    ssintub
    vy
    cA
    @0
    cU
    cK
    cV
    cX
    pclss.a
    @0
    eqid
    pclss.c
    pclvalN
    syl5sseqr
end

include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "cin.mm"
include "cv.mm"
include "cpjh.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "wss.mm"
include "chss.mm"
include "sseqin2.mm"
include "sylib.mm"
include "pjch.mm"
include "rabbi2dva.mm"
include "eqtr3d.mm"

theorem pjvec
  let vx: setvar x
  let cH: class H

  disjoint H x
  assert |- ( H e. CH -> H = { x e. ~H | ( ( projh ` H ) ` x ) = x } )

  proof
    cH
    cch
    wcel
    #
    chil
    cH
    cin
    #
    cH
    vx
    cv
    #
    cH
    cpjh
    cfv
    cfv
    @2
    wceq
    #
    vx
    chil
    crab
    @0
    cH
    chil
    wss
    @1
    cH
    wceq
    cH
    chss
    cH
    chil
    sseqin2
    sylib
    @0
    @3
    vx
    chil
    cH
    @2
    cH
    pjch
    rabbi2dva
    eqtr3d
end

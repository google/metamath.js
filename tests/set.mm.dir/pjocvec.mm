include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "cort.mm"
include "cfv.mm"
include "cin.mm"
include "cv.mm"
include "cpjh.mm"
include "c0v.mm"
include "wceq.mm"
include "crab.mm"
include "wss.mm"
include "choccl.mm"
include "chss.mm"
include "syl.mm"
include "sseqin2.mm"
include "sylib.mm"
include "pjoc2.mm"
include "rabbi2dva.mm"
include "eqtr3d.mm"

theorem pjocvec
  let vx: setvar x
  let cH: class H

  disjoint H x
  assert |- ( H e. CH -> ( _|_ ` H ) = { x e. ~H | ( ( projh ` H ) ` x ) = 0h } )

  proof
    cH
    cch
    wcel
    #
    chil
    cH
    cort
    cfv
    #
    cin
    #
    @1
    vx
    cv
    #
    cH
    cpjh
    cfv
    cfv
    c0v
    wceq
    #
    vx
    chil
    crab
    @0
    @1
    chil
    wss
    #
    @2
    @1
    wceq
    @0
    @1
    cch
    wcel
    @5
    cH
    choccl
    @1
    chss
    syl
    @1
    chil
    sseqin2
    sylib
    @0
    @4
    vx
    chil
    @1
    @3
    cH
    pjoc2
    rabbi2dva
    eqtr3d
end

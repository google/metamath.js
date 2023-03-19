include "c0.mm"
include "wne.mm"
include "ctsk.mm"
include "wcel.mm"
include "cv.mm"
include "wex.mm"
include "wi.mm"
include "n0.mm"
include "wss.mm"
include "0ss.mm"
include "tskss.mm"
include "mp3an3.mm"
include "expcom.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "impcom.mm"

theorem tsk0
  let cT: class T
  let vx: setvar x


  assert |- ( ( T e. Tarski /\ T =/= (/) ) -> (/) e. T )

  proof
    cT
    c0
    wne
    #
    cT
    ctsk
    wcel
    #
    c0
    cT
    wcel
    #
    @0
    vx
    cv
    #
    cT
    wcel
    #
    vx
    wex
    @1
    @2
    wi
    #
    vx
    cT
    n0
    @4
    @5
    vx
    @1
    @4
    @2
    @1
    @4
    c0
    @3
    wss
    @2
    @3
    0ss
    @3
    c0
    cT
    tskss
    mp3an3
    expcom
    exlimiv
    sylbi
    impcom
end

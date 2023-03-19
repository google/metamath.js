include "c0.mm"
include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "wex.mm"
include "cab.mm"
include "wnel.mm"
include "cspr.mm"
include "cfv.mm"
include "spr0nelg.mm"
include "wcel.mm"
include "wn.mm"
include "sprssspr.mm"
include "sseli.mm"
include "con3i.mm"
include "df-nel.mm"
include "3imtr4i.mm"
include "ax-mp.mm"

theorem spr0el
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vp: setvar p
  let cW: class W
  let vk: setvar k
  let vx: setvar x


  assert |- (/) e/ ( Pairs ` V )

  proof
    c0
    vp
    cv
    va
    cv
    vb
    cv
    cpr
    wceq
    vb
    wex
    va
    wex
    vp
    cab
    #
    wnel
    #
    c0
    cV
    cspr
    cfv
    #
    wnel
    #
    vp
    va
    vb
    spr0nelg
    c0
    @0
    wcel
    #
    wn
    c0
    @2
    wcel
    #
    wn
    @1
    @3
    @5
    @4
    @2
    @0
    c0
    cV
    vp
    va
    vb
    sprssspr
    sseli
    con3i
    c0
    @0
    df-nel
    c0
    @2
    df-nel
    3imtr4i
    ax-mp
end

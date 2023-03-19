include "cv.mm"
include "c0.mm"
include "wceq.mm"
include "csuc.mm"
include "con0.mm"
include "wrex.mm"
include "wo.mm"
include "wlim.mm"
include "wn.mm"
include "wcel.mm"
include "word.mm"
include "wb.mm"
include "eloni.mm"
include "dflim3.mm"
include "baib.mm"
include "con2bid.mm"
include "syl.mm"
include "rabbiia.mm"

theorem nlimon
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- { x e. On | ( x = (/) \/ E. y e. On x = suc y ) } = { x e. On | -. Lim x }

  proof
    vx
    cv
    #
    c0
    wceq
    @0
    vy
    cv
    csuc
    wceq
    vy
    con0
    wrex
    wo
    #
    @0
    wlim
    #
    wn
    #
    vx
    con0
    @0
    con0
    wcel
    @0
    word
    #
    @1
    @3
    wb
    @0
    eloni
    @4
    @2
    @1
    @2
    @4
    @1
    wn
    vy
    @0
    dflim3
    baib
    con2bid
    syl
    rabbiia
end

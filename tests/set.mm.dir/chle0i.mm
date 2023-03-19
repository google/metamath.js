include "cch.mm"
include "wcel.mm"
include "c0h.mm"
include "wss.mm"
include "wceq.mm"
include "wb.mm"
include "chle0.mm"
include "ax-mp.mm"

theorem chle0i
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  assume ch0le.1: |- A e. CH


  assert |- ( A C_ 0H <-> A = 0H )

  proof
    cA
    cch
    wcel
    cA
    c0h
    wss
    cA
    c0h
    wceq
    wb
    ch0le.1
    cA
    chle0
    ax-mp
end

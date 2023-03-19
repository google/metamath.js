include "cch.mm"
include "wcel.mm"
include "c0h.mm"
include "wss.mm"
include "ch0le.mm"
include "ax-mp.mm"

theorem ch0lei
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  assume ch0le.1: |- A e. CH


  assert |- 0H C_ A

  proof
    cA
    cch
    wcel
    c0h
    cA
    wss
    ch0le.1
    cA
    ch0le
    ax-mp
end

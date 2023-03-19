include "csh.mm"
include "wcel.mm"
include "cort.mm"
include "cfv.mm"
include "cin.mm"
include "c0h.mm"
include "wceq.mm"
include "chshii.mm"
include "ocin.mm"
include "ax-mp.mm"

theorem chocini
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  assume ch0le.1: |- A e. CH


  assert |- ( A i^i ( _|_ ` A ) ) = 0H

  proof
    cA
    csh
    wcel
    cA
    cA
    cort
    cfv
    cin
    c0h
    wceq
    cA
    ch0le.1
    chshii
    cA
    ocin
    ax-mp
end

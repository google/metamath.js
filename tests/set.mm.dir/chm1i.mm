include "chil.mm"
include "wss.mm"
include "cin.mm"
include "wceq.mm"
include "chssii.mm"
include "df-ss.mm"
include "mpbi.mm"

theorem chm1i
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  assume ch0le.1: |- A e. CH


  assert |- ( A i^i ~H ) = A

  proof
    cA
    chil
    wss
    cA
    chil
    cin
    cA
    wceq
    cA
    ch0le.1
    chssii
    cA
    chil
    df-ss
    mpbi
end

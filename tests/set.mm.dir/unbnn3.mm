include "com.mm"
include "cvv.mm"
include "wcel.mm"
include "wss.mm"
include "wel.mm"
include "wrex.mm"
include "wral.mm"
include "cen.mm"
include "wbr.mm"
include "omex.mm"
include "unbnn.mm"
include "mp3an1.mm"

theorem unbnn3
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( ( A C_ _om /\ A. x e. _om E. y e. A x e. y ) -> A ~~ _om )

  proof
    com
    cvv
    wcel
    cA
    com
    wss
    vx
    vy
    wel
    vy
    cA
    wrex
    vx
    com
    wral
    cA
    com
    cen
    wbr
    omex
    vx
    vy
    cA
    unbnn
    mp3an1
end

include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "wpo.mm"
include "cv.mm"
include "wss.mm"
include "wor.mm"
include "wa.mm"
include "wbr.mm"
include "weq.mm"
include "wo.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wal.mm"
include "wn.mm"
include "cvv.mm"
include "numth3.mm"
include "ax-mp.mm"
include "zorn2g.mm"
include "mp3an1.mm"

theorem zorn2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cR: class R
  assume zornn0.1: |- A e. _V

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  assert |- ( ( R Po A /\ A. w ( ( w C_ A /\ R Or w ) -> E. x e. A A. z e. w ( z R x \/ z = x ) ) ) -> E. x e. A A. y e. A -. x R y )

  proof
    cA
    ccrd
    cdm
    wcel
    #
    cA
    cR
    wpo
    vw
    cv
    #
    cA
    wss
    @1
    cR
    wor
    wa
    vz
    cv
    vx
    cv
    #
    cR
    wbr
    vz
    vx
    weq
    wo
    vz
    @1
    wral
    vx
    cA
    wrex
    wi
    vw
    wal
    @2
    vy
    cv
    cR
    wbr
    wn
    vy
    cA
    wral
    vx
    cA
    wrex
    cA
    cvv
    wcel
    @0
    zornn0.1
    cA
    cvv
    numth3
    ax-mp
    vx
    vy
    vz
    vw
    cA
    cR
    zorn2g
    mp3an1
end

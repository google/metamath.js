include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "crpss.mm"
include "wor.mm"
include "wa.mm"
include "cuni.mm"
include "wi.mm"
include "wal.mm"
include "wpss.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "cvv.mm"
include "numth3.mm"
include "ax-mp.mm"
include "zorng.mm"
include "mpan.mm"

theorem zorn
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vw: setvar w
  let cR: class R
  assume zornn0.1: |- A e. _V

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  assert |- ( A. z ( ( z C_ A /\ [C.] Or z ) -> U. z e. A ) -> E. x e. A A. y e. A -. x C. y )

  proof
    cA
    ccrd
    cdm
    wcel
    #
    vz
    cv
    #
    cA
    wss
    @1
    crpss
    wor
    wa
    @1
    cuni
    cA
    wcel
    wi
    vz
    wal
    vx
    cv
    vy
    cv
    wpss
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
    cA
    zorng
    mpan
end

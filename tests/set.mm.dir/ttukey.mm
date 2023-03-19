include "cuni.mm"
include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wss.mm"
include "wb.mm"
include "wal.mm"
include "wpss.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "cvv.mm"
include "uniex.mm"
include "numth3.mm"
include "ax-mp.mm"
include "ttukeyg.mm"
include "mp3an1.mm"

theorem ttukey
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume ttukey.1: |- A e. _V

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( ( A =/= (/) /\ A. x ( x e. A <-> ( ~P x i^i Fin ) C_ A ) ) -> E. x e. A A. y e. A -. x C. y )

  proof
    cA
    cuni
    #
    ccrd
    cdm
    wcel
    #
    cA
    c0
    wne
    vx
    cv
    #
    cA
    wcel
    @2
    cpw
    cfn
    cin
    cA
    wss
    wb
    vx
    wal
    @2
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
    @0
    cvv
    wcel
    @1
    cA
    ttukey.1
    uniex
    @0
    cvv
    numth3
    ax-mp
    vx
    vy
    cA
    ttukeyg
    mp3an1
end

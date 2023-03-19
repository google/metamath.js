include "cv.mm"
include "cpw.mm"
include "ciun.mm"
include "cuni.mm"
include "wss.mm"
include "wrex.mm"
include "wcel.mm"
include "ssiun.mm"
include "eliun.mm"
include "selpw.mm"
include "rexbii.mm"
include "bitri.mm"
include "uniiun.mm"
include "sseq2i.mm"
include "3imtr4i.mm"
include "ssriv.mm"

theorem iunpwss
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- U_ x e. A ~P x C_ ~P U. A

  proof
    vy
    vx
    cA
    vx
    cv
    #
    cpw
    #
    ciun
    #
    cA
    cuni
    #
    cpw
    #
    vy
    cv
    #
    @0
    wss
    #
    vx
    cA
    wrex
    #
    @5
    vx
    cA
    @0
    ciun
    #
    wss
    #
    @5
    @2
    wcel
    #
    @5
    @4
    wcel
    #
    vx
    cA
    @0
    @5
    ssiun
    @10
    @5
    @1
    wcel
    #
    vx
    cA
    wrex
    @7
    vx
    @5
    cA
    @1
    eliun
    @12
    @6
    vx
    cA
    vy
    @0
    selpw
    rexbii
    bitri
    @11
    @5
    @3
    wss
    @9
    vy
    @3
    selpw
    @3
    @8
    @5
    vx
    cA
    uniiun
    sseq2i
    bitri
    3imtr4i
    ssriv
end

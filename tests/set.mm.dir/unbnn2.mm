include "cv.mm"
include "wss.mm"
include "wrex.mm"
include "com.mm"
include "wral.mm"
include "cvv.mm"
include "wcel.mm"
include "cen.mm"
include "wbr.mm"
include "csuc.mm"
include "peano2.mm"
include "wceq.mm"
include "sseq1.mm"
include "rexbidv.mm"
include "rspcv.mm"
include "wi.mm"
include "vex.mm"
include "sucssel.mm"
include "ax-mp.mm"
include "reximi.mm"
include "syl6com.mm"
include "syl5.mm"
include "ralrimiv.mm"
include "unbnn.mm"
include "syl3an3.mm"

theorem unbnn2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint y z
  disjoint A z
  assert |- ( ( _om e. _V /\ A C_ _om /\ A. x e. _om E. y e. A x C_ y ) -> A ~~ _om )

  proof
    vx
    cv
    #
    vy
    cv
    #
    wss
    #
    vy
    cA
    wrex
    #
    vx
    com
    wral
    #
    com
    cvv
    wcel
    cA
    com
    wss
    vz
    cv
    #
    @1
    wcel
    #
    vy
    cA
    wrex
    #
    vz
    com
    wral
    cA
    com
    cen
    wbr
    @4
    @7
    vz
    com
    @5
    com
    wcel
    @5
    csuc
    #
    com
    wcel
    #
    @4
    @7
    @5
    peano2
    @9
    @4
    @8
    @1
    wss
    #
    vy
    cA
    wrex
    #
    @7
    @3
    @11
    vx
    @8
    com
    @0
    @8
    wceq
    @2
    @10
    vy
    cA
    @0
    @8
    @1
    sseq1
    rexbidv
    rspcv
    @10
    @6
    vy
    cA
    @5
    cvv
    wcel
    @10
    @6
    wi
    vz
    vex
    @5
    @1
    cvv
    sucssel
    ax-mp
    reximi
    syl6com
    syl5
    ralrimiv
    vz
    vy
    cA
    unbnn
    syl3an3
end

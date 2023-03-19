include "cv.mm"
include "wss.mm"
include "cdif.mm"
include "cun.mm"
include "cvv.mm"
include "wcel.mm"
include "vex.mm"
include "difexg.mm"
include "ax-mp.mm"
include "unex.mm"
include "sseq1.mm"
include "ssdifss.mm"
include "wa.mm"
include "unss.mm"
include "biimpi.mm"
include "syl2an.mm"
include "cllem0.mm"

theorem sssymdifcl
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  assume ssficl.a: |- A = { z | z C_ B }

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint B z
  assert |- A. x e. A A. y e. A ( ( x \ y ) u. ( y \ x ) ) e. A

  proof
    vz
    cv
    #
    cB
    wss
    vx
    cv
    #
    vy
    cv
    #
    cdif
    #
    @2
    @1
    cdif
    #
    cun
    #
    cB
    wss
    #
    @1
    cB
    wss
    #
    @2
    cB
    wss
    #
    vx
    vy
    vz
    @5
    cvv
    cA
    ssficl.a
    @3
    @4
    @1
    cvv
    wcel
    @3
    cvv
    wcel
    vx
    vex
    @1
    @2
    cvv
    difexg
    ax-mp
    @2
    cvv
    wcel
    @4
    cvv
    wcel
    vy
    vex
    @2
    @1
    cvv
    difexg
    ax-mp
    unex
    @0
    @5
    cB
    sseq1
    @0
    @1
    cB
    sseq1
    @0
    @2
    cB
    sseq1
    @7
    @3
    cB
    wss
    #
    @4
    cB
    wss
    #
    @6
    @8
    @1
    cB
    @2
    ssdifss
    @2
    cB
    @1
    ssdifss
    @9
    @10
    wa
    @6
    @3
    @4
    cB
    unss
    biimpi
    syl2an
    cllem0
end

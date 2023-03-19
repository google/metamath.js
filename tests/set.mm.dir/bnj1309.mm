include "cv.mm"
include "wss.mm"
include "c-bnj14.mm"
include "wral.mm"
include "wa.mm"
include "cab.mm"
include "hbra1.mm"
include "bnj1352.mm"
include "hbab.mm"
include "hbxfreq.mm"

theorem bnj1309
  let vx: setvar x
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cR: class R
  let vd: setvar d
  assume bnj1309.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }

  disjoint A x
  disjoint d x
  disjoint w x
  assert |- ( w e. B -> A. x w e. B )

  proof
    vx
    vw
    cB
    vd
    cv
    #
    cA
    wss
    #
    cA
    cR
    vx
    cv
    c-bnj14
    @0
    wss
    #
    vx
    @0
    wral
    #
    wa
    #
    vd
    cab
    bnj1309.1
    @4
    vx
    vd
    vw
    @1
    @3
    vx
    @2
    vx
    @0
    hbra1
    bnj1352
    hbab
    hbxfreq
end

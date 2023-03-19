include "wcel.mm"
include "ctop.mm"
include "cv.mm"
include "wss.mm"
include "cuni.mm"
include "wi.mm"
include "wal.mm"
include "cin.mm"
include "wral.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "cfn.mm"
include "w3a.mm"
include "cint.mm"
include "istopg.mm"
include "fiint.mm"
include "anbi2i.mm"
include "syl6bb.mm"

theorem istop2g
  let vx: setvar x
  let cA: class A
  let cJ: class J
  let vy: setvar y
  let vz: setvar z

  disjoint J x
  disjoint A x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint J y
  disjoint J z
  assert |- ( J e. A -> ( J e. Top <-> ( A. x ( x C_ J -> U. x e. J ) /\ A. x ( ( x C_ J /\ x =/= (/) /\ x e. Fin ) -> |^| x e. J ) ) ) )

  proof
    cJ
    cA
    wcel
    cJ
    ctop
    wcel
    vx
    cv
    #
    cJ
    wss
    #
    @0
    cuni
    cJ
    wcel
    wi
    vx
    wal
    #
    @0
    vy
    cv
    cin
    cJ
    wcel
    vy
    cJ
    wral
    vx
    cJ
    wral
    #
    wa
    @2
    @1
    @0
    c0
    wne
    @0
    cfn
    wcel
    w3a
    @0
    cint
    cJ
    wcel
    wi
    vx
    wal
    #
    wa
    vx
    vy
    cA
    cJ
    istopg
    @3
    @4
    @2
    vx
    vy
    cJ
    fiint
    anbi2i
    syl6bb
end

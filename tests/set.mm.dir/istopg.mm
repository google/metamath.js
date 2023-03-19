include "wcel.mm"
include "ctop.mm"
include "cv.mm"
include "cuni.mm"
include "cpw.mm"
include "wral.mm"
include "cin.mm"
include "wa.mm"
include "wss.mm"
include "wi.mm"
include "wal.mm"
include "wceq.mm"
include "pweq.mm"
include "eleq2.mm"
include "raleqbidv.mm"
include "raleqbi1dv.mm"
include "anbi12d.mm"
include "df-top.mm"
include "elab2g.mm"
include "df-ral.mm"
include "elpw2g.mm"
include "imbi1d.mm"
include "albidv.mm"
include "syl5bb.mm"
include "anbi1d.mm"
include "bitrd.mm"

theorem istopg
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cJ: class J
  let vz: setvar z

  disjoint x y
  disjoint J x
  disjoint J y
  disjoint A x
  disjoint x z
  disjoint y z
  disjoint J z
  assert |- ( J e. A -> ( J e. Top <-> ( A. x ( x C_ J -> U. x e. J ) /\ A. x e. J A. y e. J ( x i^i y ) e. J ) ) )

  proof
    cJ
    cA
    wcel
    #
    cJ
    ctop
    wcel
    vx
    cv
    #
    cuni
    #
    cJ
    wcel
    #
    vx
    cJ
    cpw
    #
    wral
    #
    @1
    vy
    cv
    cin
    #
    cJ
    wcel
    #
    vy
    cJ
    wral
    #
    vx
    cJ
    wral
    #
    wa
    #
    @1
    cJ
    wss
    #
    @3
    wi
    #
    vx
    wal
    #
    @9
    wa
    @2
    vz
    cv
    #
    wcel
    #
    vx
    @14
    cpw
    #
    wral
    #
    @6
    @14
    wcel
    #
    vy
    @14
    wral
    #
    vx
    @14
    wral
    #
    wa
    @10
    vz
    cJ
    ctop
    cA
    @14
    cJ
    wceq
    #
    @17
    @5
    @20
    @9
    @21
    @15
    @3
    vx
    @16
    @4
    @14
    cJ
    pweq
    @14
    cJ
    @2
    eleq2
    raleqbidv
    @19
    @8
    vx
    @14
    cJ
    @18
    @7
    vy
    @14
    cJ
    @14
    cJ
    @6
    eleq2
    raleqbi1dv
    raleqbi1dv
    anbi12d
    vz
    vx
    vy
    df-top
    elab2g
    @0
    @5
    @13
    @9
    @5
    @1
    @4
    wcel
    #
    @3
    wi
    #
    vx
    wal
    @0
    @13
    @3
    vx
    @4
    df-ral
    @0
    @23
    @12
    vx
    @0
    @22
    @11
    @3
    @1
    cJ
    cA
    elpw2g
    imbi1d
    albidv
    syl5bb
    anbi1d
    bitrd
end

include "wcel.mm"
include "ctg.mm"
include "cfv.mm"
include "cv.mm"
include "cpw.mm"
include "cin.mm"
include "cuni.mm"
include "wss.mm"
include "cab.mm"
include "tgval.mm"
include "eleq2d.mm"
include "cvv.mm"
include "elex.mm"
include "adantl.mm"
include "inex1g.mm"
include "uniexg.mm"
include "syl.mm"
include "ssexg.mm"
include "sylan2.mm"
include "ancoms.mm"
include "wceq.mm"
include "id.mm"
include "pweq.mm"
include "ineq2d.mm"
include "unieqd.mm"
include "sseq12d.mm"
include "elabg.mm"
include "pm5.21nd.mm"
include "bitrd.mm"

theorem eltg
  let cA: class A
  let cB: class B
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cJ: class J
  let cC: class C


  assert |- ( B e. V -> ( A e. ( topGen ` B ) <-> A C_ U. ( B i^i ~P A ) ) )

  proof
    cB
    cV
    wcel
    #
    cA
    cB
    ctg
    cfv
    #
    wcel
    cA
    vx
    cv
    #
    cB
    @2
    cpw
    #
    cin
    #
    cuni
    #
    wss
    #
    vx
    cab
    #
    wcel
    #
    cA
    cB
    cA
    cpw
    #
    cin
    #
    cuni
    #
    wss
    #
    @0
    @1
    @7
    cA
    vx
    cB
    cV
    tgval
    eleq2d
    @0
    @8
    @12
    cA
    cvv
    wcel
    #
    @8
    @13
    @0
    cA
    @7
    elex
    adantl
    @12
    @0
    @13
    @0
    @12
    @11
    cvv
    wcel
    #
    @13
    @0
    @10
    cvv
    wcel
    @14
    cB
    @9
    cV
    inex1g
    @10
    cvv
    uniexg
    syl
    cA
    @11
    cvv
    ssexg
    sylan2
    ancoms
    @6
    @12
    vx
    cA
    cvv
    @2
    cA
    wceq
    #
    @2
    cA
    @5
    @11
    @15
    id
    @15
    @4
    @10
    @15
    @3
    @9
    cB
    @2
    cA
    pweq
    ineq2d
    unieqd
    sseq12d
    elabg
    pm5.21nd
    bitrd
end

include "c0.mm"
include "wne.mm"
include "cv.mm"
include "crnk.mm"
include "cfv.mm"
include "wss.mm"
include "wral.mm"
include "crab.mm"
include "ciun.mm"
include "cin.mm"
include "wi.mm"
include "wex.mm"
include "eqid.mm"
include "cplem1.mm"
include "scottex.mm"
include "iunex.mm"
include "wceq.mm"
include "nfiu1.mm"
include "nfeq2.mm"
include "ineq2.mm"
include "neeq1d.mm"
include "imbi2d.mm"
include "ralbid.mm"
include "spcev.mm"
include "ax-mp.mm"

theorem cplem2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  let vw: setvar w
  assume cplem2.1: |- A e. _V

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B z
  disjoint B w
  assert |- E. y A. x e. A ( B =/= (/) -> ( B i^i y ) =/= (/) )

  proof
    cB
    c0
    wne
    #
    cB
    vx
    cA
    vz
    cv
    crnk
    cfv
    vw
    cv
    crnk
    cfv
    wss
    vw
    cB
    wral
    vz
    cB
    crab
    #
    ciun
    #
    cin
    #
    c0
    wne
    #
    wi
    #
    vx
    cA
    wral
    #
    @0
    cB
    vy
    cv
    #
    cin
    #
    c0
    wne
    #
    wi
    #
    vx
    cA
    wral
    #
    vy
    wex
    vx
    vz
    vw
    cA
    cB
    @1
    @2
    @1
    eqid
    @2
    eqid
    cplem1
    @11
    @6
    vy
    @2
    vx
    cA
    @1
    cplem2.1
    vz
    vw
    cB
    scottex
    iunex
    @7
    @2
    wceq
    #
    @10
    @5
    vx
    cA
    vx
    @7
    @2
    vx
    cA
    @1
    nfiu1
    nfeq2
    @12
    @9
    @4
    @0
    @12
    @8
    @3
    c0
    @7
    @2
    cB
    ineq2
    neeq1d
    imbi2d
    ralbid
    spcev
    ax-mp
end

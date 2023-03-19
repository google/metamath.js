include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wa.mm"
include "cz.mm"
include "crio.mm"
include "cr.mm"
include "cfl.mm"
include "wceq.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "riotabidv.mm"
include "df-fl.mm"
include "riotaex.mm"
include "fvmpt.mm"

theorem flval
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( A e. RR -> ( |_ ` A ) = ( iota_ x e. ZZ ( x <_ A /\ A < ( x + 1 ) ) ) )

  proof
    vy
    cA
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    @1
    @0
    c1
    caddc
    co
    #
    clt
    wbr
    #
    wa
    #
    vx
    cz
    crio
    @0
    cA
    cle
    wbr
    #
    cA
    @3
    clt
    wbr
    #
    wa
    #
    vx
    cz
    crio
    cr
    cfl
    @1
    cA
    wceq
    #
    @5
    @8
    vx
    cz
    @9
    @2
    @6
    @4
    @7
    @1
    cA
    @0
    cle
    breq2
    @1
    cA
    @3
    clt
    breq1
    anbi12d
    riotabidv
    vy
    vx
    df-fl
    @8
    vx
    cz
    riotaex
    fvmpt
end

include "cuo.mm"
include "wcel.mm"
include "chil.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wfo.mm"
include "elunop.mm"
include "simprbi.mm"
include "3ad2ant1.mm"
include "wi.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "rspc2v.mm"
include "3adant1.mm"
include "mpd.mm"

theorem unop
  let cA: class A
  let cB: class B
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cS: class S


  assert |- ( ( T e. UniOp /\ A e. ~H /\ B e. ~H ) -> ( ( T ` A ) .ih ( T ` B ) ) = ( A .ih B ) )

  proof
    cT
    cuo
    wcel
    #
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    w3a
    vx
    cv
    #
    cT
    cfv
    #
    vy
    cv
    #
    cT
    cfv
    #
    csp
    co
    #
    @3
    @5
    csp
    co
    #
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    #
    cA
    cT
    cfv
    #
    cB
    cT
    cfv
    #
    csp
    co
    #
    cA
    cB
    csp
    co
    #
    wceq
    #
    @0
    @1
    @10
    @2
    @0
    chil
    chil
    cT
    wfo
    @10
    vx
    vy
    cT
    elunop
    simprbi
    3ad2ant1
    @1
    @2
    @10
    @15
    wi
    @0
    @9
    @15
    @11
    @6
    csp
    co
    #
    cA
    @5
    csp
    co
    #
    wceq
    vx
    vy
    cA
    cB
    chil
    chil
    @3
    cA
    wceq
    #
    @7
    @16
    @8
    @17
    @18
    @4
    @11
    @6
    csp
    @3
    cA
    cT
    fveq2
    oveq1d
    @3
    cA
    @5
    csp
    oveq1
    eqeq12d
    @5
    cB
    wceq
    #
    @16
    @13
    @17
    @14
    @19
    @6
    @12
    @11
    csp
    @5
    cB
    cT
    fveq2
    oveq2d
    @5
    cB
    cA
    csp
    oveq2
    eqeq12d
    rspc2v
    3adant1
    mpd
end

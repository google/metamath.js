include "cho.mm"
include "wcel.mm"
include "chil.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wf.mm"
include "elhmop.mm"
include "simprbi.mm"
include "3ad2ant1.mm"
include "wi.mm"
include "oveq1.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "rspc2v.mm"
include "3adant1.mm"
include "mpd.mm"

theorem hmop
  let cA: class A
  let cB: class B
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cS: class S


  assert |- ( ( T e. HrmOp /\ A e. ~H /\ B e. ~H ) -> ( A .ih ( T ` B ) ) = ( ( T ` A ) .ih B ) )

  proof
    cT
    cho
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
    cT
    cfv
    #
    @4
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
    cB
    cT
    cfv
    #
    csp
    co
    #
    cA
    cT
    cfv
    #
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
    wf
    @10
    vx
    vy
    cT
    elhmop
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
    cA
    @5
    csp
    co
    #
    @13
    @4
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
    @6
    @16
    @8
    @17
    @3
    cA
    @5
    csp
    oveq1
    @18
    @7
    @13
    @4
    csp
    @3
    cA
    cT
    fveq2
    oveq1d
    eqeq12d
    @4
    cB
    wceq
    #
    @16
    @12
    @17
    @14
    @19
    @5
    @11
    cA
    csp
    @4
    cB
    cT
    fveq2
    oveq2d
    @4
    cB
    @13
    csp
    oveq2
    eqeq12d
    rspc2v
    3adant1
    mpd
end

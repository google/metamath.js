include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "cmpt.mm"
include "wb.mm"
include "wal.mm"
include "cvv.mm"
include "crab.mm"
include "simpl.mm"
include "eqvisset.mm"
include "adantl.mm"
include "jca.mm"
include "rabid.mm"
include "sylibr.mm"
include "syl6eleqr.mm"
include "simpr.mm"
include "ssrab2f.mm"
include "eqsstri.mm"
include "id.mm"
include "sseldi.mm"
include "adantr.mm"
include "impbii.mm"
include "ax-gen.mm"
include "eqopab2b.mm"
include "mpbir.mm"
include "df-mpt.mm"
include "3eqtr4i.mm"

theorem mptssid
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  assume mptssid.1: |- F/_ x A
  assume mptssid.2: |- C = { x e. A | B e. _V }


  assert |- ( x e. A |-> B ) = ( x e. C |-> B )

  proof
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    cB
    wceq
    #
    wa
    #
    vx
    vy
    copab
    #
    @0
    cC
    wcel
    #
    @2
    wa
    #
    vx
    vy
    copab
    #
    vx
    cA
    cB
    cmpt
    vx
    cC
    cB
    cmpt
    @4
    @7
    wceq
    @3
    @6
    wb
    #
    vy
    wal
    #
    vx
    wal
    @9
    vx
    @8
    vy
    @3
    @6
    @3
    @5
    @2
    @3
    @0
    cB
    cvv
    wcel
    #
    vx
    cA
    crab
    #
    cC
    @3
    @1
    @10
    wa
    @0
    @11
    wcel
    @3
    @1
    @10
    @1
    @2
    simpl
    @2
    @10
    @1
    vy
    cB
    eqvisset
    adantl
    jca
    @10
    vx
    cA
    rabid
    sylibr
    mptssid.2
    syl6eleqr
    @1
    @2
    simpr
    jca
    @6
    @1
    @2
    @5
    @1
    @2
    @5
    cC
    cA
    @0
    cC
    @11
    cA
    mptssid.2
    @10
    vx
    cA
    mptssid.1
    ssrab2f
    eqsstri
    @5
    id
    sseldi
    adantr
    @5
    @2
    simpr
    jca
    impbii
    ax-gen
    ax-gen
    @3
    @6
    vx
    vy
    eqopab2b
    mpbir
    vx
    vy
    cA
    cB
    df-mpt
    vx
    vy
    cC
    cB
    df-mpt
    3eqtr4i
end

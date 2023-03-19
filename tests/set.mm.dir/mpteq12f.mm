include "wceq.mm"
include "wal.mm"
include "wral.mm"
include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "copab.mm"
include "cmpt.mm"
include "nfa1.mm"
include "nfra1.mm"
include "nfan.mm"
include "nfv.mm"
include "rspa.mm"
include "eqeq2d.mm"
include "pm5.32da.mm"
include "sp.mm"
include "eleq2d.mm"
include "anbi1d.mm"
include "sylan9bbr.mm"
include "opabbid.mm"
include "df-mpt.mm"
include "3eqtr4g.mm"

theorem mpteq12f
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vy: setvar y
  let wph: wff ph


  assert |- ( ( A. x A = C /\ A. x e. A B = D ) -> ( x e. A |-> B ) = ( x e. C |-> D ) )

  proof
    cA
    cC
    wceq
    #
    vx
    wal
    #
    cB
    cD
    wceq
    #
    vx
    cA
    wral
    #
    wa
    #
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cB
    wceq
    #
    wa
    #
    vx
    vy
    copab
    @5
    cC
    wcel
    #
    @7
    cD
    wceq
    #
    wa
    #
    vx
    vy
    copab
    vx
    cA
    cB
    cmpt
    vx
    cC
    cD
    cmpt
    @4
    @9
    @12
    vx
    vy
    @1
    @3
    vx
    @0
    vx
    nfa1
    @2
    vx
    cA
    nfra1
    nfan
    @4
    vy
    nfv
    @3
    @9
    @6
    @11
    wa
    @1
    @12
    @3
    @6
    @8
    @11
    @3
    @6
    wa
    cB
    cD
    @7
    @2
    vx
    cA
    rspa
    eqeq2d
    pm5.32da
    @1
    @6
    @10
    @11
    @1
    cA
    cC
    @5
    @0
    vx
    sp
    eleq2d
    anbi1d
    sylan9bbr
    opabbid
    vx
    vy
    cA
    cB
    df-mpt
    vx
    vy
    cC
    cD
    df-mpt
    3eqtr4g
end

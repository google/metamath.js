include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wex.mm"
include "elvv.mm"
include "wfun.mm"
include "csn.mm"
include "funsn.mm"
include "funeq.mm"
include "mpbiri.mm"
include "ax-mp.mm"
include "wa.mm"
include "vex.mm"
include "funop.mm"
include "syl6bb.mm"
include "wi.mm"
include "eqeq2.mm"
include "eqeq1.mm"
include "opex.mm"
include "sneqr.mm"
include "opth.mm"
include "eqtr3.mm"
include "a1d.mm"
include "sylbi.mm"
include "syl.mm"
include "syl6bi.mm"
include "com23.mm"
include "impcom.mm"
include "exlimiv.mm"
include "com12.mm"
include "sylbid.mm"
include "mpi.mm"
include "exlimivv.mm"
include "necon3ai.mm"

theorem funsndifnop
  let cA: class A
  let cB: class B
  let cG: class G
  let va: setvar a
  let vx: setvar x
  let vy: setvar y
  assume funsndifnop.a: |- A e. _V
  assume funsndifnop.b: |- B e. _V
  assume funsndifnop.g: |- G = { <. A , B >. }


  assert |- ( A =/= B -> -. G e. ( _V X. _V ) )

  proof
    cG
    cvv
    cvv
    cxp
    wcel
    #
    cA
    cB
    @0
    cG
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    wceq
    #
    vy
    wex
    vx
    wex
    cA
    cB
    wceq
    #
    vx
    vy
    cG
    elvv
    @4
    @5
    vx
    vy
    @4
    cG
    wfun
    #
    @5
    cG
    cA
    cB
    cop
    #
    csn
    #
    wceq
    #
    @6
    funsndifnop.g
    @9
    @6
    @8
    wfun
    cA
    cB
    funsndifnop.a
    funsndifnop.b
    funsn
    cG
    @8
    funeq
    mpbiri
    ax-mp
    @4
    @6
    @1
    va
    cv
    #
    csn
    wceq
    #
    @3
    @10
    @10
    cop
    #
    csn
    #
    wceq
    #
    wa
    #
    va
    wex
    #
    @5
    @4
    @6
    @3
    wfun
    @16
    cG
    @3
    funeq
    @1
    @2
    va
    vx
    vex
    vy
    vex
    funop
    syl6bb
    @16
    @4
    @5
    @15
    @4
    @5
    wi
    #
    va
    @14
    @11
    @17
    @14
    @4
    @11
    @5
    @14
    @4
    cG
    @13
    wceq
    #
    @11
    @5
    wi
    #
    @3
    @13
    cG
    eqeq2
    @9
    @18
    @19
    wi
    funsndifnop.g
    @9
    @18
    @8
    @13
    wceq
    #
    @19
    cG
    @8
    @13
    eqeq1
    @20
    @7
    @12
    wceq
    #
    @19
    @7
    @12
    cA
    cB
    opex
    sneqr
    @21
    cA
    @10
    wceq
    cB
    @10
    wceq
    wa
    #
    @19
    cA
    cB
    @10
    @10
    funsndifnop.a
    funsndifnop.b
    opth
    @22
    @5
    @11
    cA
    cB
    @10
    eqtr3
    a1d
    sylbi
    syl
    syl6bi
    ax-mp
    syl6bi
    com23
    impcom
    exlimiv
    com12
    sylbid
    mpi
    exlimivv
    sylbi
    necon3ai
end

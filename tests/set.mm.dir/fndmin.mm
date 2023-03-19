include "wfn.mm"
include "wa.mm"
include "cin.mm"
include "cdm.mm"
include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "copab.mm"
include "crab.mm"
include "cmpt.mm"
include "dffn5.mm"
include "biimpi.mm"
include "df-mpt.mm"
include "syl6eq.mm"
include "ineqan12d.mm"
include "inopab.mm"
include "dmeqd.mm"
include "wex.mm"
include "cab.mm"
include "19.42v.mm"
include "anandi.mm"
include "exbii.mm"
include "fvex.mm"
include "eqeq1.mm"
include "ceqsexv.mm"
include "anbi2i.mm"
include "3bitr3i.mm"
include "abbii.mm"
include "dmopab.mm"
include "df-rab.mm"
include "3eqtr4i.mm"

theorem fndmin
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cG: class G
  let vy: setvar y

  disjoint F x
  disjoint G x
  disjoint A x
  disjoint F y
  disjoint x y
  disjoint G y
  disjoint A y
  assert |- ( ( F Fn A /\ G Fn A ) -> dom ( F i^i G ) = { x e. A | ( F ` x ) = ( G ` x ) } )

  proof
    cF
    cA
    wfn
    #
    cG
    cA
    wfn
    #
    wa
    #
    cF
    cG
    cin
    #
    cdm
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    @4
    cF
    cfv
    #
    wceq
    #
    wa
    #
    @5
    @6
    @4
    cG
    cfv
    #
    wceq
    #
    wa
    #
    wa
    #
    vx
    vy
    copab
    #
    cdm
    #
    @7
    @10
    wceq
    #
    vx
    cA
    crab
    #
    @2
    @3
    @14
    @2
    @3
    @9
    vx
    vy
    copab
    #
    @12
    vx
    vy
    copab
    #
    cin
    @14
    @0
    @1
    cF
    @18
    cG
    @19
    @0
    cF
    vx
    cA
    @7
    cmpt
    #
    @18
    @0
    cF
    @20
    wceq
    vx
    cA
    cF
    dffn5
    biimpi
    vx
    vy
    cA
    @7
    df-mpt
    syl6eq
    @1
    cG
    vx
    cA
    @10
    cmpt
    #
    @19
    @1
    cG
    @21
    wceq
    vx
    cA
    cG
    dffn5
    biimpi
    vx
    vy
    cA
    @10
    df-mpt
    syl6eq
    ineqan12d
    @9
    @12
    vx
    vy
    inopab
    syl6eq
    dmeqd
    @13
    vy
    wex
    #
    vx
    cab
    @5
    @16
    wa
    #
    vx
    cab
    @15
    @17
    @22
    @23
    vx
    @5
    @8
    @11
    wa
    #
    wa
    #
    vy
    wex
    @5
    @24
    vy
    wex
    #
    wa
    @22
    @23
    @5
    @24
    vy
    19.42v
    @25
    @13
    vy
    @5
    @8
    @11
    anandi
    exbii
    @26
    @16
    @5
    @11
    @16
    vy
    @7
    @4
    cF
    fvex
    @6
    @7
    @10
    eqeq1
    ceqsexv
    anbi2i
    3bitr3i
    abbii
    @13
    vx
    vy
    dmopab
    @16
    vx
    cA
    df-rab
    3eqtr4i
    syl6eq
end

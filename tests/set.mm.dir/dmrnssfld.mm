include "cdm.mm"
include "crn.mm"
include "cuni.mm"
include "cv.mm"
include "wcel.mm"
include "cop.mm"
include "wex.mm"
include "vex.mm"
include "eldm2.mm"
include "cpr.mm"
include "prid1.mm"
include "wss.mm"
include "uniop.mm"
include "uniopel.mm"
include "syl5eqelr.mm"
include "elssuni.mm"
include "syl.mm"
include "sseld.mm"
include "mpi.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "ssriv.mm"
include "elrn2.mm"
include "prid2.mm"
include "unssi.mm"

theorem dmrnssfld
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( dom A u. ran A ) C_ U. U. A

  proof
    cA
    cdm
    #
    cA
    crn
    #
    cA
    cuni
    #
    cuni
    #
    vx
    @0
    @3
    vx
    cv
    #
    @0
    wcel
    @4
    vy
    cv
    #
    cop
    #
    cA
    wcel
    #
    vy
    wex
    @4
    @3
    wcel
    #
    vy
    @4
    cA
    vx
    vex
    #
    eldm2
    @7
    @8
    vy
    @7
    @4
    @4
    @5
    cpr
    #
    wcel
    @8
    @4
    @5
    @9
    prid1
    @7
    @10
    @3
    @4
    @7
    @10
    @2
    wcel
    @10
    @3
    wss
    @7
    @10
    @6
    cuni
    @2
    @4
    @5
    @9
    vy
    vex
    #
    uniop
    @4
    @5
    cA
    @9
    @11
    uniopel
    syl5eqelr
    @10
    @2
    elssuni
    syl
    #
    sseld
    mpi
    exlimiv
    sylbi
    ssriv
    vy
    @1
    @3
    @5
    @1
    wcel
    @7
    vx
    wex
    @5
    @3
    wcel
    #
    vx
    @5
    cA
    @11
    elrn2
    @7
    @13
    vx
    @7
    @5
    @10
    wcel
    @13
    @4
    @5
    @11
    prid2
    @7
    @10
    @3
    @5
    @12
    sseld
    mpi
    exlimiv
    sylbi
    ssriv
    unssi
end

include "wrel.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "cab.mm"
include "df-opab.mm"
include "eqtri.mm"
include "abeq2i.mm"
include "simpl.mm"
include "2eximi.mm"
include "sylbi.mm"
include "ax6evr.mm"
include "pm3.21.mm"
include "eximdv.mm"
include "mpi.mm"
include "opeq2.mm"
include "eqtr2.mm"
include "eqcomd.mm"
include "sylan.mm"
include "eximi.mm"
include "syl.mm"
include "eqcoms.mm"
include "excomim.mm"
include "vex.mm"
include "pm3.2i.mm"
include "jctr.mm"
include "df-xp.mm"
include "sylibr.mm"
include "3syl.mm"
include "ax5e.mm"
include "ssriv.mm"
include "df-rel.mm"
include "mpbir.mm"

theorem relopabi
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let vu: setvar u
  assume relopabi.1: |- A = { <. x , y >. | ph }


  assert |- Rel A

  proof
    cA
    wrel
    cA
    cvv
    cvv
    cxp
    #
    wss
    vz
    cA
    @0
    vz
    cv
    #
    cA
    wcel
    #
    @1
    @0
    wcel
    #
    vy
    wex
    #
    @3
    @2
    @1
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
    #
    @1
    @5
    vu
    cv
    #
    cop
    #
    wceq
    #
    vu
    wex
    #
    vx
    wex
    #
    vy
    wex
    #
    @4
    @2
    @8
    wph
    wa
    #
    vy
    wex
    vx
    wex
    #
    @9
    @17
    vz
    cA
    cA
    wph
    vx
    vy
    copab
    @17
    vz
    cab
    relopabi.1
    wph
    vx
    vy
    vz
    df-opab
    eqtri
    abeq2i
    @16
    @8
    vx
    vy
    @8
    wph
    simpl
    2eximi
    sylbi
    @9
    @13
    vy
    wex
    vx
    wex
    @15
    @8
    @13
    vx
    vy
    @13
    @7
    @1
    @7
    @1
    wceq
    #
    @6
    @10
    wceq
    #
    @18
    wa
    #
    vu
    wex
    #
    @13
    @18
    @19
    vu
    wex
    @21
    vu
    vy
    ax6evr
    @18
    @19
    @20
    vu
    @18
    @19
    pm3.21
    eximdv
    mpi
    @20
    @12
    vu
    @19
    @7
    @11
    wceq
    #
    @18
    @12
    @6
    @10
    @5
    opeq2
    @22
    @18
    wa
    @11
    @1
    @7
    @11
    @1
    eqtr2
    eqcomd
    sylan
    eximi
    syl
    eqcoms
    2eximi
    @13
    vx
    vy
    excomim
    syl
    @14
    @3
    vy
    @14
    @12
    @5
    cvv
    wcel
    #
    @10
    cvv
    wcel
    #
    wa
    #
    wa
    #
    vu
    wex
    vx
    wex
    #
    @3
    @12
    @26
    vx
    vu
    @12
    @25
    @23
    @24
    vx
    vex
    vu
    vex
    pm3.2i
    jctr
    2eximi
    @27
    vz
    @0
    @0
    @25
    vx
    vu
    copab
    @27
    vz
    cab
    vx
    vu
    cvv
    cvv
    df-xp
    @25
    vx
    vu
    vz
    df-opab
    eqtri
    abeq2i
    sylibr
    eximi
    3syl
    @3
    vy
    ax5e
    syl
    ssriv
    cA
    df-rel
    mpbir
end

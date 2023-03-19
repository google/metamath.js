include "cint.mm"
include "csh.mm"
include "wcel.mm"
include "chil.mm"
include "wss.mm"
include "c0v.mm"
include "wa.mm"
include "cv.mm"
include "cva.mm"
include "co.mm"
include "wral.mm"
include "csm.mm"
include "cc.mm"
include "c0.mm"
include "wne.mm"
include "simpri.mm"
include "wex.mm"
include "n0.mm"
include "intss1.mm"
include "simpli.mm"
include "sseli.mm"
include "shss.mm"
include "syl.mm"
include "sstrd.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "ax-mp.mm"
include "ax-hv0cl.mm"
include "elexi.mm"
include "elint2.mm"
include "sh0.mm"
include "mprgbir.mm"
include "pm3.2i.mm"
include "elinti.mm"
include "com12.mm"
include "shaddcl.mm"
include "syl3an1.mm"
include "3expib.mm"
include "syl2and.mm"
include "ralrimiv.mm"
include "ovex.mm"
include "sylibr.mm"
include "rgen2a.mm"
include "shmulcl.mm"
include "sylan2d.mm"
include "rgen2.mm"
include "issh2.mm"
include "mpbir2an.mm"

theorem shintcli
  let cA: class A
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cD: class D
  assume shintcl.1: |- ( A C_ SH /\ A =/= (/) )


  assert |- |^| A e. SH

  proof
    cA
    cint
    #
    csh
    wcel
    @0
    chil
    wss
    #
    c0v
    @0
    wcel
    #
    wa
    vx
    cv
    #
    vy
    cv
    #
    cva
    co
    #
    @0
    wcel
    #
    vy
    @0
    wral
    vx
    @0
    wral
    #
    @3
    @4
    csm
    co
    #
    @0
    wcel
    #
    vy
    @0
    wral
    vx
    cc
    wral
    #
    wa
    @1
    @2
    cA
    c0
    wne
    #
    @1
    cA
    csh
    wss
    #
    @11
    shintcl.1
    simpri
    @11
    vz
    cv
    #
    cA
    wcel
    #
    vz
    wex
    @1
    vz
    cA
    n0
    @14
    @1
    vz
    @14
    @0
    @13
    chil
    @13
    cA
    intss1
    @14
    @13
    csh
    wcel
    #
    @13
    chil
    wss
    cA
    csh
    @13
    @12
    @11
    shintcl.1
    simpli
    sseli
    #
    @13
    shss
    syl
    sstrd
    exlimiv
    sylbi
    ax-mp
    @2
    c0v
    @13
    wcel
    #
    vz
    cA
    vz
    c0v
    cA
    c0v
    chil
    ax-hv0cl
    elexi
    elint2
    @14
    @15
    @17
    @16
    @13
    sh0
    syl
    mprgbir
    pm3.2i
    @7
    @10
    @6
    vx
    vy
    @0
    @3
    @0
    wcel
    #
    @4
    @0
    wcel
    #
    wa
    #
    @5
    @13
    wcel
    #
    vz
    cA
    wral
    @6
    @20
    @21
    vz
    cA
    @14
    @20
    @21
    @14
    @18
    @3
    @13
    wcel
    #
    @19
    @4
    @13
    wcel
    #
    @21
    @18
    @14
    @22
    @3
    cA
    @13
    elinti
    com12
    @19
    @14
    @23
    @4
    cA
    @13
    elinti
    com12
    #
    @14
    @22
    @23
    @21
    @14
    @15
    @22
    @23
    @21
    @16
    @3
    @4
    @13
    shaddcl
    syl3an1
    3expib
    syl2and
    com12
    ralrimiv
    vz
    @5
    cA
    @3
    @4
    cva
    ovex
    elint2
    sylibr
    rgen2a
    @9
    vx
    vy
    cc
    @0
    @3
    cc
    wcel
    #
    @19
    wa
    #
    @8
    @13
    wcel
    #
    vz
    cA
    wral
    @9
    @26
    @27
    vz
    cA
    @14
    @26
    @27
    @14
    @19
    @23
    @25
    @27
    @24
    @14
    @25
    @23
    @27
    @14
    @15
    @25
    @23
    @27
    @16
    @3
    @4
    @13
    shmulcl
    syl3an1
    3expib
    sylan2d
    com12
    ralrimiv
    vz
    @8
    cA
    @3
    @4
    csm
    ovex
    elint2
    sylibr
    rgen2
    pm3.2i
    vx
    vy
    @0
    issh2
    mpbir2an
end

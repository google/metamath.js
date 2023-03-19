include "cn0.mm"
include "wcel.mm"
include "cc.mm"
include "ccnfld.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmg.mm"
include "co.mm"
include "cexp.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "oveq1.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "eqid.mm"
include "cnfldbas.mm"
include "mgpbas.mm"
include "cnfld1.mm"
include "ringidval.mm"
include "mulg0.mm"
include "exp0.mm"
include "eqtr4d.mm"
include "wa.mm"
include "cmul.mm"
include "cmnd.mm"
include "crg.mm"
include "cnring.mm"
include "ringmgp.mm"
include "ax-mp.mm"
include "cnfldmul.mm"
include "mgpplusg.mm"
include "mulgnn0p1.mm"
include "mp3an1.mm"
include "ancoms.mm"
include "expp1.mm"
include "syl5ibr.mm"
include "expcom.mm"
include "a2d.mm"
include "nn0ind.mm"
include "impcom.mm"

theorem cnfldexp
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. CC /\ B e. NN0 ) -> ( B ( .g ` ( mulGrp ` CCfld ) ) A ) = ( A ^ B ) )

  proof
    cB
    cn0
    wcel
    cA
    cc
    wcel
    #
    cB
    cA
    ccnfld
    cmgp
    cfv
    #
    cmg
    cfv
    #
    co
    #
    cA
    cB
    cexp
    co
    #
    wceq
    #
    @0
    vx
    cv
    #
    cA
    @2
    co
    #
    cA
    @6
    cexp
    co
    #
    wceq
    #
    wi
    @0
    cc0
    cA
    @2
    co
    #
    cA
    cc0
    cexp
    co
    #
    wceq
    #
    wi
    @0
    vy
    cv
    #
    cA
    @2
    co
    #
    cA
    @13
    cexp
    co
    #
    wceq
    #
    wi
    @0
    @13
    c1
    caddc
    co
    #
    cA
    @2
    co
    #
    cA
    @17
    cexp
    co
    #
    wceq
    #
    wi
    @0
    @5
    wi
    vx
    vy
    cB
    @6
    cc0
    wceq
    #
    @9
    @12
    @0
    @21
    @7
    @10
    @8
    @11
    @6
    cc0
    cA
    @2
    oveq1
    @6
    cc0
    cA
    cexp
    oveq2
    eqeq12d
    imbi2d
    @6
    @13
    wceq
    #
    @9
    @16
    @0
    @22
    @7
    @14
    @8
    @15
    @6
    @13
    cA
    @2
    oveq1
    @6
    @13
    cA
    cexp
    oveq2
    eqeq12d
    imbi2d
    @6
    @17
    wceq
    #
    @9
    @20
    @0
    @23
    @7
    @18
    @8
    @19
    @6
    @17
    cA
    @2
    oveq1
    @6
    @17
    cA
    cexp
    oveq2
    eqeq12d
    imbi2d
    @6
    cB
    wceq
    #
    @9
    @5
    @0
    @24
    @7
    @3
    @8
    @4
    @6
    cB
    cA
    @2
    oveq1
    @6
    cB
    cA
    cexp
    oveq2
    eqeq12d
    imbi2d
    @0
    @10
    c1
    @11
    cc
    @2
    @1
    cA
    c1
    cc
    ccnfld
    @1
    @1
    eqid
    #
    cnfldbas
    mgpbas
    #
    ccnfld
    c1
    @1
    @25
    cnfld1
    ringidval
    @2
    eqid
    #
    mulg0
    cA
    exp0
    eqtr4d
    @13
    cn0
    wcel
    #
    @0
    @16
    @20
    @0
    @28
    @16
    @20
    wi
    @16
    @20
    @0
    @28
    wa
    #
    @14
    cA
    cmul
    co
    #
    @15
    cA
    cmul
    co
    #
    wceq
    @14
    @15
    cA
    cmul
    oveq1
    @29
    @18
    @30
    @19
    @31
    @28
    @0
    @18
    @30
    wceq
    #
    @1
    cmnd
    wcel
    #
    @28
    @0
    @32
    ccnfld
    crg
    wcel
    @33
    cnring
    ccnfld
    @1
    @25
    ringmgp
    ax-mp
    cc
    cmul
    @2
    @1
    @13
    cA
    @26
    @27
    ccnfld
    cmul
    @1
    @25
    cnfldmul
    mgpplusg
    mulgnn0p1
    mp3an1
    ancoms
    cA
    @13
    expp1
    eqeq12d
    syl5ibr
    expcom
    a2d
    nn0ind
    impcom
end

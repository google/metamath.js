include "cc.mm"
include "wcel.mm"
include "cz.mm"
include "ccnfld.mm"
include "cmg.mm"
include "cfv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "cv.mm"
include "cc0.mm"
include "cneg.mm"
include "c1.mm"
include "caddc.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "cnfldbas.mm"
include "cnfld0.mm"
include "eqid.mm"
include "mulg0.mm"
include "mul02.mm"
include "eqtr4d.mm"
include "cn0.mm"
include "wi.mm"
include "wa.mm"
include "cmnd.mm"
include "crg.mm"
include "cnring.mm"
include "ringmnd.mm"
include "ax-mp.mm"
include "cnfldadd.mm"
include "mulgnn0p1.mm"
include "mp3an1.mm"
include "nn0cn.mm"
include "adantr.mm"
include "1cnd.mm"
include "simpr.mm"
include "adddird.mm"
include "mulid2.mm"
include "adantl.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "syl5ibr.mm"
include "expcom.mm"
include "cn.mm"
include "cminusg.mm"
include "fveq2.mm"
include "mulgnegnn.mm"
include "nncn.mm"
include "mulneg1.mm"
include "sylan.mm"
include "mulcl.mm"
include "cnfldneg.mm"
include "syl.mm"
include "zindd.mm"
include "impcom.mm"

theorem cnfldmulg
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. ZZ /\ B e. CC ) -> ( A ( .g ` CCfld ) B ) = ( A x. B ) )

  proof
    cB
    cc
    wcel
    #
    cA
    cz
    wcel
    cA
    cB
    ccnfld
    cmg
    cfv
    #
    co
    #
    cA
    cB
    cmul
    co
    #
    wceq
    #
    vx
    cv
    #
    cB
    @1
    co
    #
    @5
    cB
    cmul
    co
    #
    wceq
    cc0
    cB
    @1
    co
    #
    cc0
    cB
    cmul
    co
    #
    wceq
    vy
    cv
    #
    cB
    @1
    co
    #
    @10
    cB
    cmul
    co
    #
    wceq
    #
    @10
    cneg
    #
    cB
    @1
    co
    #
    @14
    cB
    cmul
    co
    #
    wceq
    #
    @10
    c1
    caddc
    co
    #
    cB
    @1
    co
    #
    @18
    cB
    cmul
    co
    #
    wceq
    #
    @4
    @0
    vx
    vy
    cA
    @5
    cc0
    wceq
    @6
    @8
    @7
    @9
    @5
    cc0
    cB
    @1
    oveq1
    @5
    cc0
    cB
    cmul
    oveq1
    eqeq12d
    @5
    @10
    wceq
    @6
    @11
    @7
    @12
    @5
    @10
    cB
    @1
    oveq1
    @5
    @10
    cB
    cmul
    oveq1
    eqeq12d
    @5
    @18
    wceq
    @6
    @19
    @7
    @20
    @5
    @18
    cB
    @1
    oveq1
    @5
    @18
    cB
    cmul
    oveq1
    eqeq12d
    @5
    @14
    wceq
    @6
    @15
    @7
    @16
    @5
    @14
    cB
    @1
    oveq1
    @5
    @14
    cB
    cmul
    oveq1
    eqeq12d
    @5
    cA
    wceq
    @6
    @2
    @7
    @3
    @5
    cA
    cB
    @1
    oveq1
    @5
    cA
    cB
    cmul
    oveq1
    eqeq12d
    @0
    @8
    cc0
    @9
    cc
    @1
    ccnfld
    cB
    cc0
    cnfldbas
    cnfld0
    @1
    eqid
    #
    mulg0
    cB
    mul02
    eqtr4d
    @10
    cn0
    wcel
    #
    @0
    @13
    @21
    wi
    @13
    @21
    @23
    @0
    wa
    #
    @11
    cB
    caddc
    co
    #
    @12
    cB
    caddc
    co
    #
    wceq
    @11
    @12
    cB
    caddc
    oveq1
    @24
    @19
    @25
    @20
    @26
    ccnfld
    cmnd
    wcel
    #
    @23
    @0
    @19
    @25
    wceq
    ccnfld
    crg
    wcel
    @27
    cnring
    ccnfld
    ringmnd
    ax-mp
    cc
    caddc
    @1
    ccnfld
    @10
    cB
    cnfldbas
    @22
    cnfldadd
    mulgnn0p1
    mp3an1
    @24
    @20
    @12
    c1
    cB
    cmul
    co
    #
    caddc
    co
    @26
    @24
    @10
    c1
    cB
    @23
    @10
    cc
    wcel
    #
    @0
    @10
    nn0cn
    adantr
    @24
    1cnd
    @23
    @0
    simpr
    adddird
    @24
    @28
    cB
    @12
    caddc
    @0
    @28
    cB
    wceq
    @23
    cB
    mulid2
    adantl
    oveq2d
    eqtrd
    eqeq12d
    syl5ibr
    expcom
    @10
    cn
    wcel
    #
    @0
    @13
    @17
    wi
    @13
    @17
    @30
    @0
    wa
    #
    @11
    ccnfld
    cminusg
    cfv
    #
    cfv
    #
    @12
    @32
    cfv
    #
    wceq
    @11
    @12
    @32
    fveq2
    @31
    @15
    @33
    @16
    @34
    cc
    @1
    ccnfld
    @32
    @10
    cB
    cnfldbas
    @22
    @32
    eqid
    mulgnegnn
    @31
    @16
    @12
    cneg
    #
    @34
    @30
    @29
    @0
    @16
    @35
    wceq
    @10
    nncn
    #
    @10
    cB
    mulneg1
    sylan
    @31
    @12
    cc
    wcel
    #
    @34
    @35
    wceq
    @30
    @29
    @0
    @37
    @36
    @10
    cB
    mulcl
    sylan
    @12
    cnfldneg
    syl
    eqtr4d
    eqeq12d
    syl5ibr
    expcom
    zindd
    impcom
end

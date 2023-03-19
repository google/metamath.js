include "cnv.mm"
include "wcel.mm"
include "cc.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "wo.mm"
include "wa.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "c1.mm"
include "cdiv.mm"
include "oveq2.mm"
include "ad2antlr.mm"
include "cmul.mm"
include "recid2.mm"
include "oveq1d.mm"
include "3ad2antl2.mm"
include "simpl1.mm"
include "reccl.mm"
include "simpl2.mm"
include "simpl3.mm"
include "nvsass.mm"
include "syl13anc.mm"
include "nvsid.mm"
include "3adant2.mm"
include "adantr.mm"
include "3eqtr3d.mm"
include "adantlr.mm"
include "nvsz.mm"
include "sylan2.mm"
include "anassrs.mm"
include "3adantl3.mm"
include "ex.mm"
include "syl5bir.mm"
include "orrd.mm"
include "wi.mm"
include "nv0.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "3adant3.mm"
include "jaod.mm"
include "impbid.mm"

theorem nvmul0or
  let cA: class A
  let cB: class B
  let cS: class S
  let cU: class U
  let cX: class X
  let cZ: class Z
  assume nvmul0or.1: |- X = ( BaseSet ` U )
  assume nvmul0or.4: |- S = ( .sOLD ` U )
  assume nvmul0or.6: |- Z = ( 0vec ` U )


  assert |- ( ( U e. NrmCVec /\ A e. CC /\ B e. X ) -> ( ( A S B ) = Z <-> ( A = 0 \/ B = Z ) ) )

  proof
    cU
    cnv
    wcel
    #
    cA
    cc
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cA
    cB
    cS
    co
    #
    cZ
    wceq
    #
    cA
    cc0
    wceq
    #
    cB
    cZ
    wceq
    #
    wo
    #
    @3
    @5
    @8
    @3
    @5
    wa
    #
    @6
    @7
    @6
    wn
    cA
    cc0
    wne
    #
    @9
    @7
    cA
    cc0
    df-ne
    @9
    @10
    @7
    @9
    @10
    wa
    c1
    cA
    cdiv
    co
    #
    @4
    cS
    co
    #
    @11
    cZ
    cS
    co
    #
    cB
    cZ
    @5
    @12
    @13
    wceq
    @3
    @10
    @4
    cZ
    @11
    cS
    oveq2
    ad2antlr
    @3
    @10
    @12
    cB
    wceq
    @5
    @3
    @10
    wa
    #
    @11
    cA
    cmul
    co
    #
    cB
    cS
    co
    #
    c1
    cB
    cS
    co
    #
    @12
    cB
    @1
    @0
    @10
    @16
    @17
    wceq
    @2
    @1
    @10
    wa
    #
    @15
    c1
    cB
    cS
    cA
    recid2
    oveq1d
    3ad2antl2
    @14
    @0
    @11
    cc
    wcel
    #
    @1
    @2
    @16
    @12
    wceq
    @0
    @1
    @2
    @10
    simpl1
    @1
    @0
    @10
    @19
    @2
    cA
    reccl
    #
    3ad2antl2
    @0
    @1
    @2
    @10
    simpl2
    @0
    @1
    @2
    @10
    simpl3
    @11
    cA
    cB
    cS
    cU
    cX
    nvmul0or.1
    nvmul0or.4
    nvsass
    syl13anc
    @3
    @17
    cB
    wceq
    #
    @10
    @0
    @2
    @21
    @1
    cB
    cS
    cU
    cX
    nvmul0or.1
    nvmul0or.4
    nvsid
    3adant2
    adantr
    3eqtr3d
    adantlr
    @3
    @10
    @13
    cZ
    wceq
    #
    @5
    @0
    @1
    @10
    @22
    @2
    @0
    @1
    @10
    @22
    @18
    @0
    @19
    @22
    @20
    @11
    cS
    cU
    cZ
    nvmul0or.4
    nvmul0or.6
    nvsz
    sylan2
    anassrs
    3adantl3
    adantlr
    3eqtr3d
    ex
    syl5bir
    orrd
    ex
    @3
    @6
    @5
    @7
    @0
    @2
    @6
    @5
    wi
    @1
    @0
    @2
    wa
    @5
    @6
    cc0
    cB
    cS
    co
    #
    cZ
    wceq
    cB
    cS
    cU
    cX
    cZ
    nvmul0or.1
    nvmul0or.4
    nvmul0or.6
    nv0
    @6
    @4
    @23
    cZ
    cA
    cc0
    cB
    cS
    oveq1
    eqeq1d
    syl5ibrcom
    3adant2
    @0
    @1
    @7
    @5
    wi
    @2
    @0
    @1
    wa
    @5
    @7
    cA
    cZ
    cS
    co
    #
    cZ
    wceq
    cA
    cS
    cU
    cZ
    nvmul0or.4
    nvmul0or.6
    nvsz
    @7
    @4
    @24
    cZ
    cB
    cZ
    cA
    cS
    oveq2
    eqeq1d
    syl5ibrcom
    3adant3
    jaod
    impbid
end

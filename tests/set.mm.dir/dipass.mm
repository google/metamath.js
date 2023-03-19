include "ccphlo.mm"
include "wcel.mm"
include "cc.mm"
include "w3a.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "wi.mm"
include "caddc.mm"
include "cop.mm"
include "cabs.mm"
include "cif.mm"
include "cba.mm"
include "cfv.mm"
include "cns.mm"
include "cdip.mm"
include "fveq2.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "3anbi23d.mm"
include "oveqd.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "cpv.mm"
include "eqid.mm"
include "elimphu.mm"
include "ipassi.mm"
include "dedth.mm"
include "imp.mm"

theorem dipass
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cS: class S
  let cU: class U
  let cX: class X
  assume ipass.1: |- X = ( BaseSet ` U )
  assume ipass.4: |- S = ( .sOLD ` U )
  assume ipass.7: |- P = ( .iOLD ` U )


  assert |- ( ( U e. CPreHilOLD /\ ( A e. CC /\ B e. X /\ C e. X ) ) -> ( ( A S B ) P C ) = ( A x. ( B P C ) ) )

  proof
    cU
    ccphlo
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
    cC
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
    cC
    cP
    co
    #
    cA
    cB
    cC
    cP
    co
    #
    cmul
    co
    #
    wceq
    #
    @0
    @4
    @9
    wi
    @1
    cB
    @0
    cU
    caddc
    cmul
    cop
    cabs
    cop
    #
    cif
    #
    cba
    cfv
    #
    wcel
    #
    cC
    @12
    wcel
    #
    w3a
    #
    cA
    cB
    @11
    cns
    cfv
    #
    co
    #
    cC
    @11
    cdip
    cfv
    #
    co
    #
    cA
    cB
    cC
    @18
    co
    #
    cmul
    co
    #
    wceq
    #
    wi
    cU
    @10
    cU
    @11
    wceq
    #
    @4
    @15
    @9
    @22
    @23
    @2
    @13
    @3
    @14
    @1
    @23
    cX
    @12
    cB
    @23
    cX
    cU
    cba
    cfv
    @12
    ipass.1
    cU
    @11
    cba
    fveq2
    syl5eq
    #
    eleq2d
    @23
    cX
    @12
    cC
    @24
    eleq2d
    3anbi23d
    @23
    @6
    @19
    @8
    @21
    @23
    @6
    @17
    cC
    cP
    co
    @19
    @23
    @5
    @17
    cC
    cP
    @23
    cS
    @16
    cA
    cB
    @23
    cS
    cU
    cns
    cfv
    @16
    ipass.4
    cU
    @11
    cns
    fveq2
    syl5eq
    oveqd
    oveq1d
    @23
    cP
    @18
    @17
    cC
    @23
    cP
    cU
    cdip
    cfv
    @18
    ipass.7
    cU
    @11
    cdip
    fveq2
    syl5eq
    #
    oveqd
    eqtrd
    @23
    @7
    @20
    cA
    cmul
    @23
    cP
    @18
    cB
    cC
    @25
    oveqd
    oveq2d
    eqeq12d
    imbi12d
    cA
    cB
    cC
    @18
    @16
    @11
    @11
    cpv
    cfv
    #
    @12
    @12
    eqid
    @26
    eqid
    @16
    eqid
    @18
    eqid
    cU
    elimphu
    ipassi
    dedth
    imp
end

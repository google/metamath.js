include "ccphlo.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "wi.mm"
include "cmul.mm"
include "cop.mm"
include "cabs.mm"
include "cif.mm"
include "cba.mm"
include "cfv.mm"
include "cpv.mm"
include "cdip.mm"
include "fveq2.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "3anbi123d.mm"
include "oveqd.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "cns.mm"
include "eqid.mm"
include "elimphu.mm"
include "ipdiri.mm"
include "dedth.mm"
include "imp.mm"

theorem dipdir
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cU: class U
  let cG: class G
  let cX: class X
  assume dipdir.1: |- X = ( BaseSet ` U )
  assume dipdir.2: |- G = ( +v ` U )
  assume dipdir.7: |- P = ( .iOLD ` U )


  assert |- ( ( U e. CPreHilOLD /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A G B ) P C ) = ( ( A P C ) + ( B P C ) ) )

  proof
    cU
    ccphlo
    wcel
    #
    cA
    cX
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
    cG
    co
    #
    cC
    cP
    co
    #
    cA
    cC
    cP
    co
    #
    cB
    cC
    cP
    co
    #
    caddc
    co
    #
    wceq
    #
    @0
    @4
    @10
    wi
    cA
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
    cB
    @13
    wcel
    #
    cC
    @13
    wcel
    #
    w3a
    #
    cA
    cB
    @12
    cpv
    cfv
    #
    co
    #
    cC
    @12
    cdip
    cfv
    #
    co
    #
    cA
    cC
    @20
    co
    #
    cB
    cC
    @20
    co
    #
    caddc
    co
    #
    wceq
    #
    wi
    cU
    @11
    cU
    @12
    wceq
    #
    @4
    @17
    @10
    @25
    @26
    @1
    @14
    @2
    @15
    @3
    @16
    @26
    cX
    @13
    cA
    @26
    cX
    cU
    cba
    cfv
    @13
    dipdir.1
    cU
    @12
    cba
    fveq2
    syl5eq
    #
    eleq2d
    @26
    cX
    @13
    cB
    @27
    eleq2d
    @26
    cX
    @13
    cC
    @27
    eleq2d
    3anbi123d
    @26
    @6
    @21
    @9
    @24
    @26
    @6
    @19
    cC
    cP
    co
    @21
    @26
    @5
    @19
    cC
    cP
    @26
    cG
    @18
    cA
    cB
    @26
    cG
    cU
    cpv
    cfv
    @18
    dipdir.2
    cU
    @12
    cpv
    fveq2
    syl5eq
    oveqd
    oveq1d
    @26
    cP
    @20
    @19
    cC
    @26
    cP
    cU
    cdip
    cfv
    @20
    dipdir.7
    cU
    @12
    cdip
    fveq2
    syl5eq
    #
    oveqd
    eqtrd
    @26
    @7
    @22
    @8
    @23
    caddc
    @26
    cP
    @20
    cA
    cC
    @28
    oveqd
    @26
    cP
    @20
    cB
    cC
    @28
    oveqd
    oveq12d
    eqeq12d
    imbi12d
    cA
    cB
    cC
    @20
    @12
    cns
    cfv
    #
    @12
    @18
    @13
    @13
    eqid
    @18
    eqid
    @29
    eqid
    @20
    eqid
    cU
    elimphu
    ipdiri
    dedth
    imp
end

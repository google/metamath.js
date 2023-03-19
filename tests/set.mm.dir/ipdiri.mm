include "wcel.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cn0v.mm"
include "cfv.mm"
include "cif.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "eqid.mm"
include "elimph.mm"
include "ipdirilem.mm"
include "dedth3h.mm"

theorem ipdiri
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cS: class S
  let cU: class U
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cN: class N
  assume ip1i.1: |- X = ( BaseSet ` U )
  assume ip1i.2: |- G = ( +v ` U )
  assume ip1i.4: |- S = ( .sOLD ` U )
  assume ip1i.7: |- P = ( .iOLD ` U )
  assume ip1i.9: |- U e. CPreHilOLD


  assert |- ( ( A e. X /\ B e. X /\ C e. X ) -> ( ( A G B ) P C ) = ( ( A P C ) + ( B P C ) ) )

  proof
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
    @0
    cA
    cU
    cn0v
    cfv
    #
    cif
    #
    cB
    cG
    co
    #
    cC
    cP
    co
    #
    @9
    cC
    cP
    co
    #
    @6
    caddc
    co
    #
    wceq
    @9
    @1
    cB
    @8
    cif
    #
    cG
    co
    #
    cC
    cP
    co
    #
    @12
    @14
    cC
    cP
    co
    #
    caddc
    co
    #
    wceq
    @15
    @2
    cC
    @8
    cif
    #
    cP
    co
    #
    @9
    @19
    cP
    co
    #
    @14
    @19
    cP
    co
    #
    caddc
    co
    #
    wceq
    cA
    cB
    cC
    @8
    @8
    @8
    cA
    @9
    wceq
    #
    @4
    @11
    @7
    @13
    @24
    @3
    @10
    cC
    cP
    cA
    @9
    cB
    cG
    oveq1
    oveq1d
    @24
    @5
    @12
    @6
    caddc
    cA
    @9
    cC
    cP
    oveq1
    oveq1d
    eqeq12d
    cB
    @14
    wceq
    #
    @11
    @16
    @13
    @18
    @25
    @10
    @15
    cC
    cP
    cB
    @14
    @9
    cG
    oveq2
    oveq1d
    @25
    @6
    @17
    @12
    caddc
    cB
    @14
    cC
    cP
    oveq1
    oveq2d
    eqeq12d
    cC
    @19
    wceq
    #
    @16
    @20
    @18
    @23
    cC
    @19
    @15
    cP
    oveq2
    @26
    @12
    @21
    @17
    @22
    caddc
    cC
    @19
    @9
    cP
    oveq2
    cC
    @19
    @14
    cP
    oveq2
    oveq12d
    eqeq12d
    @9
    @14
    @19
    cP
    cS
    cU
    cG
    cX
    ip1i.1
    ip1i.2
    ip1i.4
    ip1i.7
    ip1i.9
    cA
    cU
    cX
    @8
    ip1i.1
    @8
    eqid
    #
    ip1i.9
    elimph
    cB
    cU
    cX
    @8
    ip1i.1
    @27
    ip1i.9
    elimph
    cC
    cU
    cX
    @8
    ip1i.1
    @27
    ip1i.9
    elimph
    ipdirilem
    dedth3h
end

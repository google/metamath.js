include "cc.mm"
include "wcel.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "wa.mm"
include "wi.mm"
include "cn0v.mm"
include "cfv.mm"
include "cif.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "eqid.mm"
include "elimph.mm"
include "ipasslem11.mm"
include "dedth2h.mm"
include "com12.mm"
include "3impib.mm"

theorem ipassi
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


  assert |- ( ( A e. CC /\ B e. X /\ C e. X ) -> ( ( A S B ) P C ) = ( A x. ( B P C ) ) )

  proof
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
    @1
    @2
    wa
    @0
    @7
    @1
    @2
    @0
    @7
    wi
    @0
    cA
    @1
    cB
    cU
    cn0v
    cfv
    #
    cif
    #
    cS
    co
    #
    cC
    cP
    co
    #
    cA
    @9
    cC
    cP
    co
    #
    cmul
    co
    #
    wceq
    #
    wi
    @0
    @10
    @2
    cC
    @8
    cif
    #
    cP
    co
    #
    cA
    @9
    @15
    cP
    co
    #
    cmul
    co
    #
    wceq
    #
    wi
    cB
    cC
    @8
    @8
    cB
    @9
    wceq
    #
    @7
    @14
    @0
    @20
    @4
    @11
    @6
    @13
    @20
    @3
    @10
    cC
    cP
    cB
    @9
    cA
    cS
    oveq2
    oveq1d
    @20
    @5
    @12
    cA
    cmul
    cB
    @9
    cC
    cP
    oveq1
    oveq2d
    eqeq12d
    imbi2d
    cC
    @15
    wceq
    #
    @14
    @19
    @0
    @21
    @11
    @16
    @13
    @18
    cC
    @15
    @10
    cP
    oveq2
    @21
    @12
    @17
    cA
    cmul
    cC
    @15
    @9
    cP
    oveq2
    oveq2d
    eqeq12d
    imbi2d
    @9
    @15
    cA
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
    cB
    cU
    cX
    @8
    ip1i.1
    @8
    eqid
    #
    ip1i.9
    elimph
    cC
    cU
    cX
    @8
    ip1i.1
    @22
    ip1i.9
    elimph
    ipasslem11
    dedth2h
    com12
    3impib
end

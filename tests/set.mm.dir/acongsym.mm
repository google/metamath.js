include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cneg.mm"
include "wo.mm"
include "wi.mm"
include "wa.mm"
include "congsym.mm"
include "exp32.mm"
include "3impia.mm"
include "cc.mm"
include "zcn.mm"
include "3ad2ant2.mm"
include "negnegd.mm"
include "oveq1d.mm"
include "negcld.mm"
include "3ad2ant3.mm"
include "neg2subd.mm"
include "eqtr3d.mm"
include "breq2d.mm"
include "biimpd.mm"
include "orim12d.mm"
include "imp.mm"

theorem acongsym
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) /\ ( A || ( B - C ) \/ A || ( B - -u C ) ) ) -> ( A || ( C - B ) \/ A || ( C - -u B ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    cC
    cz
    wcel
    #
    w3a
    #
    cA
    cB
    cC
    cmin
    co
    cdvds
    wbr
    #
    cA
    cB
    cC
    cneg
    #
    cmin
    co
    #
    cdvds
    wbr
    #
    wo
    cA
    cC
    cB
    cmin
    co
    cdvds
    wbr
    #
    cA
    cC
    cB
    cneg
    #
    cmin
    co
    #
    cdvds
    wbr
    #
    wo
    @3
    @4
    @8
    @7
    @11
    @0
    @1
    @2
    @4
    @8
    wi
    @0
    @1
    wa
    @2
    @4
    @8
    cA
    cB
    cC
    congsym
    exp32
    3impia
    @3
    @7
    @11
    @3
    @6
    @10
    cA
    cdvds
    @3
    @9
    cneg
    #
    @5
    cmin
    co
    @6
    @10
    @3
    @12
    cB
    @5
    cmin
    @3
    cB
    @1
    @0
    cB
    cc
    wcel
    @2
    cB
    zcn
    #
    3ad2ant2
    negnegd
    oveq1d
    @3
    @9
    cC
    @1
    @0
    @9
    cc
    wcel
    @2
    @1
    cB
    @13
    negcld
    3ad2ant2
    @2
    @0
    cC
    cc
    wcel
    @1
    cC
    zcn
    3ad2ant3
    neg2subd
    eqtr3d
    breq2d
    biimpd
    orim12d
    imp
end

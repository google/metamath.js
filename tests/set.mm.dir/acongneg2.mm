include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cneg.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "wo.mm"
include "wa.mm"
include "cc.mm"
include "zcn.mm"
include "3ad2ant3.mm"
include "negnegd.mm"
include "oveq2d.mm"
include "breq2d.mm"
include "biimpd.mm"
include "orim2d.mm"
include "imp.mm"
include "orcomd.mm"

theorem acongneg2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) /\ ( A || ( B - -u C ) \/ A || ( B - -u -u C ) ) ) -> ( A || ( B - C ) \/ A || ( B - -u C ) ) )

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
    cneg
    #
    cmin
    co
    cdvds
    wbr
    #
    cA
    cB
    @4
    cneg
    #
    cmin
    co
    #
    cdvds
    wbr
    #
    wo
    #
    wa
    @5
    cA
    cB
    cC
    cmin
    co
    #
    cdvds
    wbr
    #
    @3
    @9
    @5
    @11
    wo
    @3
    @8
    @11
    @5
    @3
    @8
    @11
    @3
    @7
    @10
    cA
    cdvds
    @3
    @6
    cC
    cB
    cmin
    @3
    cC
    @2
    @0
    cC
    cc
    wcel
    @1
    cC
    zcn
    3ad2ant3
    negnegd
    oveq2d
    breq2d
    biimpd
    orim2d
    imp
    orcomd
end

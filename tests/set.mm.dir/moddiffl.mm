include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "cmin.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cmul.mm"
include "modval.mm"
include "oveq2d.mm"
include "simpl.mm"
include "recnd.mm"
include "cc.mm"
include "rpcn.mm"
include "adantl.mm"
include "rerpdivcl.mm"
include "flcld.mm"
include "zcnd.mm"
include "mulcld.mm"
include "nncand.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "cc0.mm"
include "wne.mm"
include "rpne0.mm"
include "divcan3d.mm"

theorem moddiffl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR+ ) -> ( ( A - ( A mod B ) ) / B ) = ( |_ ` ( A / B ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    crp
    wcel
    #
    wa
    #
    cA
    cA
    cB
    cmo
    co
    #
    cmin
    co
    #
    cB
    cdiv
    co
    cB
    cA
    cB
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cB
    cdiv
    co
    @6
    @2
    @4
    @7
    cB
    cdiv
    @2
    @4
    cA
    cA
    @7
    cmin
    co
    #
    cmin
    co
    @7
    @2
    @3
    @8
    cA
    cmin
    cA
    cB
    modval
    oveq2d
    @2
    cA
    @7
    @2
    cA
    @0
    @1
    simpl
    recnd
    @2
    cB
    @6
    @1
    cB
    cc
    wcel
    @0
    cB
    rpcn
    adantl
    #
    @2
    @6
    @2
    @5
    cA
    cB
    rerpdivcl
    flcld
    zcnd
    #
    mulcld
    nncand
    eqtrd
    oveq1d
    @2
    @6
    cB
    @10
    @9
    @1
    cB
    cc0
    wne
    @0
    cB
    rpne0
    adantl
    divcan3d
    eqtrd
end

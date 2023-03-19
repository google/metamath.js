include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "cmul.mm"
include "cmo.mm"
include "caddc.mm"
include "cmin.mm"
include "wceq.mm"
include "rerpdivcl.mm"
include "flcld.mm"
include "zcnd.mm"
include "cc.mm"
include "rpcn.mm"
include "adantl.mm"
include "mulcld.mm"
include "modcl.mm"
include "recnd.mm"
include "pncand.mm"
include "addcld.mm"
include "subcld.mm"
include "cc0.mm"
include "wne.mm"
include "rpne0.mm"
include "divmul3d.mm"
include "mpbird.mm"
include "flpmodeq.mm"
include "oveq1d.mm"
include "eqtr3d.mm"

theorem fldivmod
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. RR /\ B e. RR+ ) -> ( |_ ` ( A / B ) ) = ( ( A - ( A mod B ) ) / B ) )

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
    cB
    cdiv
    co
    #
    cfl
    cfv
    #
    cB
    cmul
    co
    #
    cA
    cB
    cmo
    co
    #
    caddc
    co
    #
    @6
    cmin
    co
    #
    cB
    cdiv
    co
    #
    @4
    cA
    @6
    cmin
    co
    #
    cB
    cdiv
    co
    @2
    @9
    @4
    wceq
    @8
    @5
    wceq
    @2
    @5
    @6
    @2
    @4
    cB
    @2
    @4
    @2
    @3
    cA
    cB
    rerpdivcl
    flcld
    zcnd
    #
    @1
    cB
    cc
    wcel
    @0
    cB
    rpcn
    adantl
    #
    mulcld
    #
    @2
    @6
    cA
    cB
    modcl
    recnd
    #
    pncand
    @2
    @8
    @4
    cB
    @2
    @7
    @6
    @2
    @5
    @6
    @13
    @14
    addcld
    @14
    subcld
    @11
    @12
    @1
    cB
    cc0
    wne
    @0
    cB
    rpne0
    adantl
    divmul3d
    mpbird
    @2
    @8
    @10
    cB
    cdiv
    @2
    @7
    cA
    @6
    cmin
    cA
    cB
    flpmodeq
    oveq1d
    oveq1d
    eqtr3d
end

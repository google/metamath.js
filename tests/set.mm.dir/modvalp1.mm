include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cmul.mm"
include "cmin.mm"
include "c1.mm"
include "cmo.mm"
include "cc.mm"
include "recn.mm"
include "adantr.mm"
include "refldivcl.mm"
include "recnd.mm"
include "rpcn.mm"
include "adantl.mm"
include "mulcld.mm"
include "pnpcan2d.mm"
include "adddirp1d.mm"
include "oveq2d.mm"
include "modvalr.mm"
include "3eqtr4d.mm"

theorem modvalp1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR+ ) -> ( ( A + B ) - ( ( ( |_ ` ( A / B ) ) + 1 ) x. B ) ) = ( A mod B ) )

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
    caddc
    co
    #
    cA
    cB
    cdiv
    co
    cfl
    cfv
    #
    cB
    cmul
    co
    #
    cB
    caddc
    co
    #
    cmin
    co
    cA
    @5
    cmin
    co
    @3
    @4
    c1
    caddc
    co
    cB
    cmul
    co
    #
    cmin
    co
    cA
    cB
    cmo
    co
    @2
    cA
    @5
    cB
    @0
    cA
    cc
    wcel
    @1
    cA
    recn
    adantr
    @2
    @4
    cB
    @2
    @4
    cA
    cB
    refldivcl
    recnd
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
    @9
    pnpcan2d
    @2
    @7
    @6
    @3
    cmin
    @2
    @4
    cB
    @8
    @9
    adddirp1d
    oveq2d
    cA
    cB
    modvalr
    3eqtr4d
end

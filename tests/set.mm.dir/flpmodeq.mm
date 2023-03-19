include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "cmul.mm"
include "cmin.mm"
include "cmo.mm"
include "wceq.mm"
include "caddc.mm"
include "modvalr.mm"
include "eqcomd.mm"
include "cc.mm"
include "recn.mm"
include "adantr.mm"
include "rerpdivcl.mm"
include "flcl.mm"
include "zcnd.mm"
include "syl.mm"
include "rpcn.mm"
include "adantl.mm"
include "mulcld.mm"
include "modcl.mm"
include "recnd.mm"
include "subaddd.mm"
include "mpbid.mm"

theorem flpmodeq
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR+ ) -> ( ( ( |_ ` ( A / B ) ) x. B ) + ( A mod B ) ) = A )

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
    cmin
    co
    #
    cA
    cB
    cmo
    co
    #
    wceq
    @5
    @7
    caddc
    co
    cA
    wceq
    @2
    @7
    @6
    cA
    cB
    modvalr
    eqcomd
    @2
    cA
    @5
    @7
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
    @3
    cr
    wcel
    #
    @4
    cc
    wcel
    cA
    cB
    rerpdivcl
    @8
    @4
    @3
    flcl
    zcnd
    syl
    @1
    cB
    cc
    wcel
    @0
    cB
    rpcn
    adantl
    mulcld
    @2
    @7
    cA
    cB
    modcl
    recnd
    subaddd
    mpbid
end

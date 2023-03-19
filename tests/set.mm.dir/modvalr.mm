include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cmul.mm"
include "cmin.mm"
include "modval.mm"
include "cc.mm"
include "rpcn.mm"
include "adantl.mm"
include "rerpdivcl.mm"
include "reflcl.mm"
include "recnd.mm"
include "syl.mm"
include "mulcomd.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem modvalr
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR+ ) -> ( A mod B ) = ( A - ( ( |_ ` ( A / B ) ) x. B ) ) )

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
    cmo
    co
    cA
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
    cmin
    co
    cA
    @4
    cB
    cmul
    co
    #
    cmin
    co
    cA
    cB
    modval
    @2
    @5
    @6
    cA
    cmin
    @2
    cB
    @4
    @1
    cB
    cc
    wcel
    @0
    cB
    rpcn
    adantl
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
    @7
    @4
    @3
    reflcl
    recnd
    syl
    mulcomd
    oveq2d
    eqtrd
end

include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "rpgecl.mm"
include "rpcn.mm"
include "rpne0.mm"
include "dividd.mm"
include "eqcomd.mm"
include "syl.mm"
include "simp3.mm"
include "simp1.mm"
include "lediv2d.mm"
include "mpbid.mm"
include "eqbrtrd.mm"

theorem divge1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR+ /\ B e. RR /\ A <_ B ) -> 1 <_ ( B / A ) )

  proof
    cA
    crp
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    w3a
    #
    c1
    cB
    cB
    cdiv
    co
    #
    cB
    cA
    cdiv
    co
    #
    cle
    @3
    cB
    crp
    wcel
    #
    c1
    @4
    wceq
    cA
    cB
    rpgecl
    #
    @6
    @4
    c1
    @6
    cB
    cB
    rpcn
    cB
    rpne0
    dividd
    eqcomd
    syl
    @3
    @2
    @4
    @5
    cle
    wbr
    @0
    @1
    @2
    simp3
    @3
    cA
    cB
    cB
    @0
    @1
    @2
    simp1
    @7
    @7
    lediv2d
    mpbid
    eqbrtrd
end

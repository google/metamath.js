include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "cz.mm"
include "cneg.mm"
include "cmo.mm"
include "cc0.mm"
include "wceq.mm"
include "cc.mm"
include "wb.mm"
include "rerpdivcl.mm"
include "recn.mm"
include "znegclb.mm"
include "3syl.mm"
include "adantr.mm"
include "rpcn.mm"
include "adantl.mm"
include "wne.mm"
include "rpne0.mm"
include "divnegd.mm"
include "eleq1d.mm"
include "bitrd.mm"
include "mod0.mm"
include "renegcl.mm"
include "sylan.mm"
include "3bitr4d.mm"

theorem negmod0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR+ ) -> ( ( A mod B ) = 0 <-> ( -u A mod B ) = 0 ) )

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
    cz
    wcel
    #
    cA
    cneg
    #
    cB
    cdiv
    co
    #
    cz
    wcel
    #
    cA
    cB
    cmo
    co
    cc0
    wceq
    @5
    cB
    cmo
    co
    cc0
    wceq
    #
    @2
    @4
    @3
    cneg
    #
    cz
    wcel
    #
    @7
    @2
    @3
    cr
    wcel
    @3
    cc
    wcel
    @4
    @10
    wb
    cA
    cB
    rerpdivcl
    @3
    recn
    @3
    znegclb
    3syl
    @2
    @9
    @6
    cz
    @2
    cA
    cB
    @0
    cA
    cc
    wcel
    @1
    cA
    recn
    adantr
    @1
    cB
    cc
    wcel
    @0
    cB
    rpcn
    adantl
    @1
    cB
    cc0
    wne
    @0
    cB
    rpne0
    adantl
    divnegd
    eleq1d
    bitrd
    cA
    cB
    mod0
    @0
    @5
    cr
    wcel
    @1
    @8
    @7
    wb
    cA
    renegcl
    @5
    cB
    mod0
    sylan
    3bitr4d
end

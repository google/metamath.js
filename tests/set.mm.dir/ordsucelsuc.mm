include "word.mm"
include "wcel.mm"
include "csuc.mm"
include "wa.mm"
include "simpl.mm"
include "ordelord.mm"
include "jca.mm"
include "ordsuc.mm"
include "sylibr.mm"
include "sylanb.mm"
include "cvv.mm"
include "wb.mm"
include "wi.mm"
include "wss.mm"
include "wceq.mm"
include "wo.mm"
include "ordsseleq.mm"
include "ancoms.mm"
include "adantl.mm"
include "ordsucss.mm"
include "ad2antrl.mm"
include "sucssel.mm"
include "adantr.mm"
include "impbid.mm"
include "sucexb.mm"
include "elsucg.mm"
include "sylbi.mm"
include "3bitr4d.mm"
include "ex.mm"
include "wn.mm"
include "elex.mm"
include "pm5.21ni.mm"
include "a1d.mm"
include "pm2.61i.mm"
include "pm5.21nd.mm"

theorem ordsucelsuc
  let cA: class A
  let cB: class B


  assert |- ( Ord B -> ( A e. B <-> suc A e. suc B ) )

  proof
    cB
    word
    #
    cA
    cB
    wcel
    #
    cA
    csuc
    #
    cB
    csuc
    #
    wcel
    #
    @0
    cA
    word
    #
    wa
    #
    @0
    @1
    wa
    @0
    @5
    @0
    @1
    simpl
    cB
    cA
    ordelord
    jca
    @0
    @4
    wa
    @0
    @5
    @0
    @4
    simpl
    @0
    @3
    word
    #
    @4
    @5
    cB
    ordsuc
    @7
    @4
    wa
    @2
    word
    #
    @5
    @3
    @2
    ordelord
    cA
    ordsuc
    #
    sylibr
    sylanb
    jca
    cA
    cvv
    wcel
    #
    @6
    @1
    @4
    wb
    #
    wi
    @10
    @6
    @11
    @10
    @6
    wa
    #
    @2
    cB
    wss
    #
    @2
    cB
    wcel
    @2
    cB
    wceq
    wo
    #
    @1
    @4
    @6
    @13
    @14
    wb
    #
    @10
    @5
    @0
    @15
    @5
    @8
    @0
    @15
    @9
    @2
    cB
    ordsseleq
    sylanb
    ancoms
    adantl
    @12
    @1
    @13
    @0
    @1
    @13
    wi
    @10
    @5
    cA
    cB
    ordsucss
    ad2antrl
    @10
    @13
    @1
    wi
    @6
    cA
    cB
    cvv
    sucssel
    adantr
    impbid
    @10
    @4
    @14
    wb
    #
    @6
    @10
    @2
    cvv
    wcel
    #
    @16
    cA
    sucexb
    #
    @2
    cB
    cvv
    elsucg
    sylbi
    adantr
    3bitr4d
    ex
    @10
    wn
    @11
    @6
    @1
    @10
    @4
    cA
    cB
    elex
    @4
    @17
    @10
    @2
    @3
    elex
    @18
    sylibr
    pm5.21ni
    a1d
    pm2.61i
    pm5.21nd
end

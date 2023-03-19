include "word.mm"
include "wcel.mm"
include "csuc.mm"
include "wss.mm"
include "wi.mm"
include "wa.mm"
include "ordelord.mm"
include "wn.mm"
include "ordnbtwn.mm"
include "imnan.mm"
include "sylibr.mm"
include "adantr.mm"
include "wb.mm"
include "ordsuc.mm"
include "ordtri1.mm"
include "sylanb.mm"
include "sylibrd.mm"
include "sylan.mm"
include "exp31.mm"
include "pm2.43b.mm"

theorem ordsucss
  let cA: class A
  let cB: class B


  assert |- ( Ord B -> ( A e. B -> suc A C_ B ) )

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
    wss
    #
    @1
    @0
    @1
    @3
    wi
    #
    @0
    @1
    @0
    @4
    @0
    @1
    wa
    cA
    word
    #
    @0
    @4
    cB
    cA
    ordelord
    @5
    @0
    wa
    @1
    cB
    @2
    wcel
    #
    wn
    #
    @3
    @5
    @1
    @7
    wi
    #
    @0
    @5
    @1
    @6
    wa
    wn
    @8
    cA
    cB
    ordnbtwn
    @1
    @6
    imnan
    sylibr
    adantr
    @5
    @2
    word
    @0
    @3
    @7
    wb
    cA
    ordsuc
    @2
    cB
    ordtri1
    sylanb
    sylibrd
    sylan
    exp31
    pm2.43b
    pm2.43b
end

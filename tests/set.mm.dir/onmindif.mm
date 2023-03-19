include "con0.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "csuc.mm"
include "cdif.mm"
include "cint.mm"
include "cv.mm"
include "wral.mm"
include "wn.mm"
include "eldif.mm"
include "wi.mm"
include "wb.mm"
include "ssel2.mm"
include "ontri1.mm"
include "onsssuc.mm"
include "bitr3d.mm"
include "con1bid.mm"
include "sylan.mm"
include "biimpd.mm"
include "exp31.mm"
include "com23.mm"
include "imp4b.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "elintg.mm"
include "adantl.mm"
include "mpbird.mm"

theorem onmindif
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A C_ On /\ B e. On ) -> B e. |^| ( A \ suc B ) )

  proof
    cA
    con0
    wss
    #
    cB
    con0
    wcel
    #
    wa
    #
    cB
    cA
    cB
    csuc
    #
    cdif
    #
    cint
    wcel
    #
    cB
    vx
    cv
    #
    wcel
    #
    vx
    @4
    wral
    #
    @2
    @7
    vx
    @4
    @6
    @4
    wcel
    @6
    cA
    wcel
    #
    @6
    @3
    wcel
    #
    wn
    #
    wa
    @2
    @7
    @6
    cA
    @3
    eldif
    @0
    @1
    @9
    @11
    @7
    @0
    @9
    @1
    @11
    @7
    wi
    #
    @0
    @9
    @1
    @12
    @0
    @9
    wa
    #
    @1
    wa
    @11
    @7
    @13
    @6
    con0
    wcel
    #
    @1
    @11
    @7
    wb
    cA
    con0
    @6
    ssel2
    @14
    @1
    wa
    #
    @7
    @10
    @15
    @6
    cB
    wss
    @7
    wn
    @10
    @6
    cB
    ontri1
    @6
    cB
    onsssuc
    bitr3d
    con1bid
    sylan
    biimpd
    exp31
    com23
    imp4b
    syl5bi
    ralrimiv
    @1
    @5
    @8
    wb
    @0
    vx
    cB
    @4
    con0
    elintg
    adantl
    mpbird
end

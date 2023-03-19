include "cdif.mm"
include "c0.mm"
include "wne.mm"
include "word.mm"
include "wss.mm"
include "wn.mm"
include "cint.mm"
include "wceq.mm"
include "ssdif0.mm"
include "necon3bbii.mm"
include "w3a.mm"
include "cv.mm"
include "wcel.mm"
include "crab.mm"
include "dfdif2.mm"
include "inteqi.mm"
include "wa.mm"
include "ordtri1.mm"
include "con2bid.mm"
include "wb.mm"
include "id.mm"
include "ordelord.mm"
include "syl2anr.mm"
include "an32s.mm"
include "rabbidva.mm"
include "inteqd.mm"
include "intmin.mm"
include "sylan9req.mm"
include "ex.mm"
include "sylbird.mm"
include "3impia.mm"
include "syl5req.mm"
include "syl3an3br.mm"

theorem ordintdif
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( Ord A /\ Ord B /\ ( A \ B ) =/= (/) ) -> B = |^| ( A \ B ) )

  proof
    cA
    cB
    cdif
    #
    c0
    wne
    cA
    word
    #
    cB
    word
    #
    cA
    cB
    wss
    #
    wn
    #
    cB
    @0
    cint
    #
    wceq
    @3
    @0
    c0
    cA
    cB
    ssdif0
    necon3bbii
    @1
    @2
    @4
    w3a
    @5
    vx
    cv
    #
    cB
    wcel
    wn
    #
    vx
    cA
    crab
    #
    cint
    #
    cB
    @0
    @8
    vx
    cA
    cB
    dfdif2
    inteqi
    @1
    @2
    @4
    @9
    cB
    wceq
    #
    @1
    @2
    wa
    #
    @4
    cB
    cA
    wcel
    #
    @10
    @11
    @3
    @12
    cA
    cB
    ordtri1
    con2bid
    @11
    @12
    @10
    @11
    @12
    @9
    cB
    @6
    wss
    #
    vx
    cA
    crab
    #
    cint
    cB
    @11
    @14
    @8
    @11
    @13
    @7
    vx
    cA
    @1
    @6
    cA
    wcel
    #
    @2
    @13
    @7
    wb
    #
    @2
    @2
    @6
    word
    @16
    @1
    @15
    wa
    @2
    id
    cA
    @6
    ordelord
    cB
    @6
    ordtri1
    syl2anr
    an32s
    rabbidva
    inteqd
    vx
    cB
    cA
    intmin
    sylan9req
    ex
    sylbird
    3impia
    syl5req
    syl3an3br
end

include "wcel.mm"
include "c0.mm"
include "ccda.mm"
include "co.mm"
include "cun.mm"
include "cen.mm"
include "cvv.mm"
include "cin.mm"
include "wceq.mm"
include "wbr.mm"
include "0ex.mm"
include "in0.mm"
include "cdaun.mm"
include "mp3an23.mm"
include "un0.mm"
include "syl6breq.mm"

theorem cda0en
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ( A +c (/) ) ~~ A )

  proof
    cA
    cV
    wcel
    #
    cA
    c0
    ccda
    co
    #
    cA
    c0
    cun
    #
    cA
    cen
    @0
    c0
    cvv
    wcel
    cA
    c0
    cin
    c0
    wceq
    @1
    @2
    cen
    wbr
    0ex
    cA
    in0
    cA
    c0
    cV
    cvv
    cdaun
    mp3an23
    cA
    un0
    syl6breq
end

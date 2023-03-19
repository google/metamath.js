include "wlim.mm"
include "c0.mm"
include "wcel.mm"
include "wne.mm"
include "wceq.mm"
include "nlim0.mm"
include "limeq.mm"
include "mtbiri.mm"
include "necon2ai.mm"
include "word.mm"
include "wb.mm"
include "limord.mm"
include "ord0eln0.mm"
include "syl.mm"
include "mpbird.mm"

theorem 0ellim
  let cA: class A


  assert |- ( Lim A -> (/) e. A )

  proof
    cA
    wlim
    #
    c0
    cA
    wcel
    #
    cA
    c0
    wne
    #
    @0
    cA
    c0
    cA
    c0
    wceq
    @0
    c0
    wlim
    nlim0
    cA
    c0
    limeq
    mtbiri
    necon2ai
    @0
    cA
    word
    @1
    @2
    wb
    cA
    limord
    cA
    ord0eln0
    syl
    mpbird
end

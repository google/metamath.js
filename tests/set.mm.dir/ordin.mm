include "word.mm"
include "cin.mm"
include "wtr.mm"
include "ordtr.mm"
include "trin.mm"
include "syl2an.mm"
include "wss.mm"
include "inss2.mm"
include "trssord.mm"
include "mp3an2.mm"
include "sylancom.mm"

theorem ordin
  let cA: class A
  let cB: class B


  assert |- ( ( Ord A /\ Ord B ) -> Ord ( A i^i B ) )

  proof
    cA
    word
    #
    cB
    word
    #
    cA
    cB
    cin
    #
    wtr
    #
    @2
    word
    #
    @0
    cA
    wtr
    cB
    wtr
    @3
    @1
    cA
    ordtr
    cB
    ordtr
    cA
    cB
    trin
    syl2an
    @3
    @2
    cB
    wss
    @1
    @4
    cA
    cB
    inss2
    @2
    cB
    trssord
    mp3an2
    sylancom
end

include "wcel.mm"
include "wss.mm"
include "wo.mm"
include "cun.mm"
include "con0.mm"
include "word.mm"
include "onordi.mm"
include "ordtri2or.mm"
include "mp2an.mm"
include "oneluni.mm"
include "syl6eqel.mm"
include "wceq.mm"
include "ssequn1.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "sylbi.mm"
include "jaoi.mm"
include "ax-mp.mm"

theorem onun2i
  let cA: class A
  let cB: class B
  assume on.1: |- A e. On
  assume on.2: |- B e. On


  assert |- ( A u. B ) e. On

  proof
    cB
    cA
    wcel
    #
    cA
    cB
    wss
    #
    wo
    #
    cA
    cB
    cun
    #
    con0
    wcel
    #
    cB
    word
    cA
    word
    @2
    cB
    on.2
    onordi
    cA
    on.1
    onordi
    cB
    cA
    ordtri2or
    mp2an
    @0
    @4
    @1
    @0
    @3
    cA
    con0
    cA
    cB
    on.1
    oneluni
    on.1
    syl6eqel
    @1
    @3
    cB
    wceq
    #
    @4
    cA
    cB
    ssequn1
    @5
    @4
    cB
    con0
    wcel
    on.2
    @3
    cB
    con0
    eleq1
    mpbiri
    sylbi
    jaoi
    ax-mp
end

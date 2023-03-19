include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "cuni.mm"
include "simpl.mm"
include "id.mm"
include "syl6sseq.mm"
include "adantl.mm"
include "restuni4.mm"
include "eqcomd.mm"

theorem restuni5
  let cA: class A
  let cJ: class J
  let cV: class V
  let cX: class X
  assume restuni5.1: |- X = U. J


  assert |- ( ( J e. V /\ A C_ X ) -> A = U. ( J |`t A ) )

  proof
    cJ
    cV
    wcel
    #
    cA
    cX
    wss
    #
    wa
    #
    cJ
    cA
    crest
    co
    cuni
    cA
    @2
    cJ
    cA
    cV
    @0
    @1
    simpl
    @1
    cA
    cJ
    cuni
    #
    wss
    @0
    @1
    cA
    cX
    @3
    @1
    id
    restuni5.1
    syl6sseq
    adantl
    restuni4
    eqcomd
end

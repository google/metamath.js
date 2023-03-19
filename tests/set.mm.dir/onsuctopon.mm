include "con0.mm"
include "wcel.mm"
include "csuc.mm"
include "ctop.mm"
include "cuni.mm"
include "wceq.mm"
include "ctopon.mm"
include "cfv.mm"
include "onsuctop.mm"
include "word.mm"
include "eloni.mm"
include "ordunisuc.mm"
include "eqcomd.mm"
include "syl.mm"
include "istopon.mm"
include "sylanbrc.mm"

theorem onsuctopon
  let cA: class A


  assert |- ( A e. On -> suc A e. ( TopOn ` A ) )

  proof
    cA
    con0
    wcel
    #
    cA
    csuc
    #
    ctop
    wcel
    cA
    @1
    cuni
    #
    wceq
    #
    @1
    cA
    ctopon
    cfv
    wcel
    cA
    onsuctop
    @0
    cA
    word
    #
    @3
    cA
    eloni
    @4
    @2
    cA
    cA
    ordunisuc
    eqcomd
    syl
    cA
    @1
    istopon
    sylanbrc
end

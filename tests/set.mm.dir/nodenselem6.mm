include "csur.mm"
include "wcel.mm"
include "wa.mm"
include "cbday.mm"
include "cfv.mm"
include "wceq.mm"
include "cslt.mm"
include "wbr.mm"
include "cv.mm"
include "wne.mm"
include "con0.mm"
include "crab.mm"
include "cint.mm"
include "cres.mm"
include "simpll.mm"
include "nodenselem4.mm"
include "adantrl.mm"
include "noreson.mm"
include "syl2anc.mm"

theorem nodenselem6
  let cA: class A
  let cB: class B
  let va: setvar a

  disjoint A a
  disjoint B a
  assert |- ( ( ( A e. No /\ B e. No ) /\ ( ( bday ` A ) = ( bday ` B ) /\ A <s B ) ) -> ( A |` |^| { a e. On | ( A ` a ) =/= ( B ` a ) } ) e. No )

  proof
    cA
    csur
    wcel
    #
    cB
    csur
    wcel
    #
    wa
    #
    cA
    cbday
    cfv
    cB
    cbday
    cfv
    wceq
    #
    cA
    cB
    cslt
    wbr
    #
    wa
    #
    wa
    @0
    va
    cv
    #
    cA
    cfv
    @6
    cB
    cfv
    wne
    va
    con0
    crab
    cint
    #
    con0
    wcel
    #
    cA
    @7
    cres
    csur
    wcel
    @0
    @1
    @5
    simpll
    @2
    @4
    @8
    @3
    cA
    cB
    va
    nodenselem4
    adantrl
    cA
    @7
    noreson
    syl2anc
end

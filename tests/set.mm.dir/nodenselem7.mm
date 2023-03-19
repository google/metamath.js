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
include "w3a.mm"
include "simpll.mm"
include "simplr.mm"
include "wn.mm"
include "wor.mm"
include "sltso.mm"
include "sonr.mm"
include "mpan.mm"
include "breq2.mm"
include "notbid.mm"
include "syl5ibcom.mm"
include "necon2ad.mm"
include "imp.mm"
include "ad2ant2rl.mm"
include "3jca.mm"
include "nosepeq.mm"
include "sylan.mm"
include "ex.mm"

theorem nodenselem7
  let cA: class A
  let cB: class B
  let cC: class C
  let va: setvar a

  disjoint A a
  disjoint B a
  disjoint C a
  assert |- ( ( ( A e. No /\ B e. No ) /\ ( ( bday ` A ) = ( bday ` B ) /\ A <s B ) ) -> ( C e. |^| { a e. On | ( A ` a ) =/= ( B ` a ) } -> ( A ` C ) = ( B ` C ) ) )

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
    #
    cC
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
    wcel
    #
    cC
    cA
    cfv
    cC
    cB
    cfv
    wceq
    #
    @5
    @0
    @1
    cA
    cB
    wne
    #
    w3a
    @7
    @8
    @5
    @0
    @1
    @9
    @0
    @1
    @4
    simpll
    @0
    @1
    @4
    simplr
    @0
    @3
    @9
    @1
    @2
    @0
    @3
    @9
    @0
    @3
    cA
    cB
    @0
    cA
    cA
    cslt
    wbr
    #
    wn
    #
    cA
    cB
    wceq
    #
    @3
    wn
    csur
    cslt
    wor
    @0
    @11
    sltso
    csur
    cA
    cslt
    sonr
    mpan
    @12
    @10
    @3
    cA
    cB
    cA
    cslt
    breq2
    notbid
    syl5ibcom
    necon2ad
    imp
    ad2ant2rl
    3jca
    va
    cA
    cB
    cC
    nosepeq
    sylan
    ex
end

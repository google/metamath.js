include "csur.mm"
include "wcel.mm"
include "wa.mm"
include "cslt.mm"
include "wbr.mm"
include "wne.mm"
include "cv.mm"
include "cfv.mm"
include "con0.mm"
include "crab.mm"
include "cint.mm"
include "simpll.mm"
include "simplr.mm"
include "wn.mm"
include "wceq.mm"
include "wor.mm"
include "sltso.mm"
include "sonr.mm"
include "mpan.mm"
include "adantr.mm"
include "breq2.mm"
include "notbid.mm"
include "syl5ibcom.mm"
include "necon2ad.mm"
include "imp.mm"
include "nosepon.mm"
include "syl3anc.mm"

theorem nodenselem4
  let cA: class A
  let cB: class B
  let va: setvar a

  disjoint A a
  disjoint B a
  assert |- ( ( ( A e. No /\ B e. No ) /\ A <s B ) -> |^| { a e. On | ( A ` a ) =/= ( B ` a ) } e. On )

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
    cB
    cslt
    wbr
    #
    wa
    @0
    @1
    cA
    cB
    wne
    #
    va
    cv
    #
    cA
    cfv
    @5
    cB
    cfv
    wne
    va
    con0
    crab
    cint
    con0
    wcel
    @0
    @1
    @3
    simpll
    @0
    @1
    @3
    simplr
    @2
    @3
    @4
    @2
    @3
    cA
    cB
    @2
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
    @0
    @7
    @1
    csur
    cslt
    wor
    @0
    @7
    sltso
    csur
    cA
    cslt
    sonr
    mpan
    adantr
    @8
    @6
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
    va
    cA
    cB
    nosepon
    syl3anc
end

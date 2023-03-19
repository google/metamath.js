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
include "cdm.mm"
include "cun.mm"
include "simpll.mm"
include "simplr.mm"
include "wi.mm"
include "wn.mm"
include "wor.mm"
include "sltso.mm"
include "sonr.mm"
include "mpan.mm"
include "breq2.mm"
include "notbid.mm"
include "syl5ibcom.mm"
include "necon2ad.mm"
include "adantr.mm"
include "imp.mm"
include "adantrl.mm"
include "nosepdm.mm"
include "syl3anc.mm"
include "unidm.mm"
include "simprl.mm"
include "uneq2d.mm"
include "syl5reqr.mm"
include "bdayval.mm"
include "syl.mm"
include "uneq12d.mm"
include "3eqtr3d.mm"
include "eleqtrd.mm"
include "eleqtrrd.mm"

theorem nodenselem5
  let cA: class A
  let cB: class B
  let va: setvar a

  disjoint A a
  disjoint B a
  assert |- ( ( ( A e. No /\ B e. No ) /\ ( ( bday ` A ) = ( bday ` B ) /\ A <s B ) ) -> |^| { a e. On | ( A ` a ) =/= ( B ` a ) } e. ( bday ` A ) )

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
    #
    cB
    cbday
    cfv
    #
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
    va
    cv
    #
    cA
    cfv
    @9
    cB
    cfv
    wne
    va
    con0
    crab
    cint
    #
    cA
    cdm
    #
    @3
    @8
    @10
    @11
    cB
    cdm
    #
    cun
    #
    @11
    @8
    @0
    @1
    cA
    cB
    wne
    #
    @10
    @13
    wcel
    @0
    @1
    @7
    simpll
    #
    @0
    @1
    @7
    simplr
    #
    @2
    @6
    @14
    @5
    @2
    @6
    @14
    @0
    @6
    @14
    wi
    @1
    @0
    @6
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
    @6
    wn
    csur
    cslt
    wor
    @0
    @18
    sltso
    csur
    cA
    cslt
    sonr
    mpan
    @19
    @17
    @6
    cA
    cB
    cA
    cslt
    breq2
    notbid
    syl5ibcom
    necon2ad
    adantr
    imp
    adantrl
    va
    cA
    cB
    nosepdm
    syl3anc
    @8
    @3
    @4
    cun
    #
    @3
    @13
    @11
    @8
    @3
    @3
    @3
    cun
    @20
    @3
    unidm
    @8
    @3
    @4
    @3
    @2
    @5
    @6
    simprl
    uneq2d
    syl5reqr
    @8
    @3
    @11
    @4
    @12
    @8
    @0
    @3
    @11
    wceq
    @15
    cA
    bdayval
    syl
    #
    @8
    @1
    @4
    @12
    wceq
    @16
    cB
    bdayval
    syl
    uneq12d
    @21
    3eqtr3d
    eleqtrd
    @21
    eleqtrrd
end

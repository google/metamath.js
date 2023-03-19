include "wcel.mm"
include "wa.mm"
include "ccrd.mm"
include "cfv.mm"
include "wceq.mm"
include "cen.mm"
include "wbr.mm"
include "cdm.mm"
include "numth3.mm"
include "ad2antrr.mm"
include "cardid2.mm"
include "ensym.mm"
include "3syl.mm"
include "simpr.mm"
include "ad2antlr.mm"
include "cardidd.mm"
include "eqbrtrd.mm"
include "entr.mm"
include "syl2anc.mm"
include "ex.mm"
include "carden2b.mm"
include "impbid1.mm"

theorem carden
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A e. C /\ B e. D ) -> ( ( card ` A ) = ( card ` B ) <-> A ~~ B ) )

  proof
    cA
    cC
    wcel
    #
    cB
    cD
    wcel
    #
    wa
    #
    cA
    ccrd
    cfv
    #
    cB
    ccrd
    cfv
    #
    wceq
    #
    cA
    cB
    cen
    wbr
    #
    @2
    @5
    @6
    @2
    @5
    wa
    #
    cA
    @3
    cen
    wbr
    #
    @3
    cB
    cen
    wbr
    @6
    @7
    cA
    ccrd
    cdm
    #
    wcel
    #
    @3
    cA
    cen
    wbr
    @8
    @0
    @10
    @1
    @5
    cA
    cC
    numth3
    ad2antrr
    cA
    cardid2
    @3
    cA
    ensym
    3syl
    @7
    @3
    @4
    cB
    cen
    @2
    @5
    simpr
    @7
    cB
    @9
    @1
    cB
    @9
    wcel
    @0
    @5
    cB
    cD
    numth3
    ad2antlr
    cardidd
    eqbrtrd
    cA
    @3
    cB
    entr
    syl2anc
    ex
    cA
    cB
    carden2b
    impbid1
end

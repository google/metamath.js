include "chf.mm"
include "wcel.mm"
include "cuni.mm"
include "crnk.mm"
include "cfv.mm"
include "com.mm"
include "rankuni.mm"
include "wss.mm"
include "wtr.mm"
include "rankon.mm"
include "ontrci.mm"
include "df-tr.mm"
include "mpbi.mm"
include "elhf2g.mm"
include "ibi.mm"
include "word.mm"
include "wa.mm"
include "wi.mm"
include "con0.mm"
include "eqeltrri.mm"
include "onordi.mm"
include "ordom.mm"
include "ordtr2.mm"
include "mp2an.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "cvv.mm"
include "wb.mm"
include "uniexg.mm"
include "syl.mm"
include "mpbird.mm"

theorem hfuni
  let cA: class A


  assert |- ( A e. Hf -> U. A e. Hf )

  proof
    cA
    chf
    wcel
    #
    cA
    cuni
    #
    chf
    wcel
    #
    @1
    crnk
    cfv
    #
    com
    wcel
    #
    @0
    @3
    cA
    crnk
    cfv
    #
    cuni
    #
    com
    cA
    rankuni
    #
    @0
    @6
    @5
    wss
    #
    @5
    com
    wcel
    #
    @6
    com
    wcel
    #
    @5
    wtr
    @8
    @5
    cA
    rankon
    ontrci
    @5
    df-tr
    mpbi
    @0
    @9
    cA
    chf
    elhf2g
    ibi
    @6
    word
    com
    word
    @8
    @9
    wa
    @10
    wi
    @6
    @3
    @6
    con0
    @7
    @1
    rankon
    eqeltrri
    onordi
    ordom
    @6
    @5
    com
    ordtr2
    mp2an
    sylancr
    syl5eqel
    @0
    @1
    cvv
    wcel
    @2
    @4
    wb
    cA
    chf
    uniexg
    @1
    cvv
    elhf2g
    syl
    mpbird
end

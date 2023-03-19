include "ccrd.mm"
include "cfv.mm"
include "wceq.mm"
include "com.mm"
include "wcel.mm"
include "cale.mm"
include "crn.mm"
include "wo.mm"
include "cun.mm"
include "wn.mm"
include "wss.mm"
include "word.mm"
include "con0.mm"
include "cardon.mm"
include "eleq1.mm"
include "mpbii.mm"
include "eloni.mm"
include "syl.mm"
include "ordom.mm"
include "ordtri2or.mm"
include "sylancl.mm"
include "ord.mm"
include "wa.mm"
include "isinfcard.mm"
include "biimpi.mm"
include "expcom.mm"
include "syld.mm"
include "orrd.mm"
include "cardnn.mm"
include "bicomi.mm"
include "simprbi.mm"
include "jaoi.mm"
include "impbii.mm"
include "elun.mm"
include "bitr4i.mm"

theorem iscard3
  let cA: class A


  assert |- ( ( card ` A ) = A <-> A e. ( _om u. ran aleph ) )

  proof
    cA
    ccrd
    cfv
    #
    cA
    wceq
    #
    cA
    com
    wcel
    #
    cA
    cale
    crn
    #
    wcel
    #
    wo
    #
    cA
    com
    @3
    cun
    wcel
    @1
    @5
    @1
    @2
    @4
    @1
    @2
    wn
    com
    cA
    wss
    #
    @4
    @1
    @2
    @6
    @1
    cA
    word
    #
    com
    word
    @2
    @6
    wo
    @1
    cA
    con0
    wcel
    #
    @7
    @1
    @0
    con0
    wcel
    @8
    cA
    cardon
    @0
    cA
    con0
    eleq1
    mpbii
    cA
    eloni
    syl
    ordom
    cA
    com
    ordtri2or
    sylancl
    ord
    @6
    @1
    @4
    @6
    @1
    wa
    #
    @4
    cA
    isinfcard
    #
    biimpi
    expcom
    syld
    orrd
    @2
    @1
    @4
    cA
    cardnn
    @4
    @6
    @1
    @9
    @4
    @10
    bicomi
    simprbi
    jaoi
    impbii
    cA
    com
    @3
    elun
    bitr4i
end

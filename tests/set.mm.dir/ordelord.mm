include "word.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "wi.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "ordeq.mm"
include "imbi12d.mm"
include "wtr.mm"
include "cep.mm"
include "wwe.mm"
include "wel.mm"
include "wal.mm"
include "simpll.mm"
include "w3a.mm"
include "3anrot.mm"
include "3anass.mm"
include "bitr3i.mm"
include "ordtr.mm"
include "trel3.mm"
include "syl.mm"
include "syl5bir.mm"
include "impl.mm"
include "trel.mm"
include "expcomd.mm"
include "imp31.mm"
include "adantrl.mm"
include "simplr.mm"
include "ordwe.mm"
include "wetrep.mm"
include "sylan.mm"
include "syl13anc.mm"
include "ex.mm"
include "pm2.43d.mm"
include "alrimivv.mm"
include "dftr2.mm"
include "sylibr.mm"
include "wss.mm"
include "trss.mm"
include "wess.mm"
include "syl6ci.mm"
include "imp.mm"
include "df-ord.mm"
include "sylanbrc.mm"
include "vtoclg.mm"
include "anabsi7.mm"

theorem ordelord
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( Ord A /\ B e. A ) -> Ord B )

  proof
    cA
    word
    #
    cB
    cA
    wcel
    #
    cB
    word
    #
    @0
    vx
    cv
    #
    cA
    wcel
    #
    wa
    #
    @3
    word
    #
    wi
    @0
    @1
    wa
    #
    @2
    wi
    vx
    cB
    cA
    @3
    cB
    wceq
    #
    @5
    @7
    @6
    @2
    @8
    @4
    @1
    @0
    @3
    cB
    cA
    eleq1
    anbi2d
    @3
    cB
    ordeq
    imbi12d
    @5
    @3
    wtr
    #
    @3
    cep
    wwe
    #
    @6
    @5
    vz
    vy
    wel
    #
    vy
    vx
    wel
    #
    wa
    #
    vz
    vx
    wel
    #
    wi
    #
    vy
    wal
    vz
    wal
    @9
    @5
    @15
    vz
    vy
    @5
    @13
    @14
    @5
    @13
    @15
    @5
    @13
    wa
    @0
    vz
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cA
    wcel
    #
    @4
    @15
    @0
    @4
    @13
    simpll
    @0
    @4
    @13
    @17
    @4
    @13
    wa
    #
    @11
    @12
    @4
    w3a
    #
    @0
    @17
    @21
    @4
    @11
    @12
    w3a
    @20
    @4
    @11
    @12
    3anrot
    @4
    @11
    @12
    3anass
    bitr3i
    @0
    cA
    wtr
    #
    @21
    @17
    wi
    cA
    ordtr
    #
    cA
    @16
    @18
    @3
    trel3
    syl
    syl5bir
    impl
    @5
    @12
    @19
    @11
    @0
    @4
    @12
    @19
    @0
    @12
    @4
    @19
    @0
    @22
    @12
    @4
    wa
    @19
    wi
    @23
    cA
    @18
    @3
    trel
    syl
    expcomd
    imp31
    adantrl
    @0
    @4
    @13
    simplr
    @0
    cA
    cep
    wwe
    #
    @17
    @19
    @4
    w3a
    @15
    cA
    ordwe
    #
    vz
    vy
    vx
    cA
    wetrep
    sylan
    syl13anc
    ex
    pm2.43d
    alrimivv
    vz
    vy
    @3
    dftr2
    sylibr
    @0
    @4
    @10
    @0
    @4
    @3
    cA
    wss
    #
    @24
    @10
    @0
    @22
    @4
    @26
    wi
    @23
    cA
    @3
    trss
    syl
    @25
    @3
    cA
    cep
    wess
    syl6ci
    imp
    @3
    df-ord
    sylanbrc
    vtoclg
    anabsi7
end

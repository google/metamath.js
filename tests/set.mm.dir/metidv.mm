include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "copab.mm"
include "wbr.mm"
include "cmetid.mm"
include "wb.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "oveq12.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "eqid.mm"
include "brabga.mm"
include "adantl.mm"
include "metidval.mm"
include "adantr.mm"
include "breqd.mm"
include "ibar.mm"
include "3bitr4d.mm"

theorem metidv
  let cA: class A
  let cB: class B
  let cD: class D
  let cX: class X
  let va: setvar a
  let vb: setvar b


  assert |- ( ( D e. ( PsMet ` X ) /\ ( A e. X /\ B e. X ) ) -> ( A ( ~Met ` D ) B <-> ( A D B ) = 0 ) )

  proof
    cD
    cX
    cpsmet
    cfv
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    wa
    #
    wa
    #
    cA
    cB
    va
    cv
    #
    cX
    wcel
    #
    vb
    cv
    #
    cX
    wcel
    #
    wa
    #
    @5
    @7
    cD
    co
    #
    cc0
    wceq
    #
    wa
    #
    va
    vb
    copab
    #
    wbr
    #
    @3
    cA
    cB
    cD
    co
    #
    cc0
    wceq
    #
    wa
    #
    cA
    cB
    cD
    cmetid
    cfv
    #
    wbr
    @16
    @3
    @14
    @17
    wb
    @0
    @12
    @17
    va
    vb
    cA
    cB
    @13
    cX
    cX
    @5
    cA
    wceq
    #
    @7
    cB
    wceq
    #
    wa
    #
    @9
    @3
    @11
    @16
    @19
    @6
    @1
    @20
    @8
    @2
    @5
    cA
    cX
    eleq1
    @7
    cB
    cX
    eleq1
    bi2anan9
    @21
    @10
    @15
    cc0
    @5
    cA
    @7
    cB
    cD
    oveq12
    eqeq1d
    anbi12d
    @13
    eqid
    brabga
    adantl
    @4
    @18
    @13
    cA
    cB
    @0
    @18
    @13
    wceq
    @3
    va
    vb
    cD
    cX
    metidval
    adantr
    breqd
    @3
    @16
    @17
    wb
    @0
    @3
    @16
    ibar
    adantl
    3bitr4d
end

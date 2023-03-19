include "wfun.mm"
include "c0.mm"
include "crn.mm"
include "wnel.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "cres.mm"
include "cdm.mm"
include "wss.mm"
include "fveqdmss.mm"
include "cin.mm"
include "dmres.mm"
include "incom.mm"
include "sseqin2.mm"
include "biimpi.mm"
include "syl5eq.mm"
include "syl6eq.mm"
include "syl.mm"
include "wa.mm"
include "wcel.mm"
include "fvres.mm"
include "adantl.mm"
include "id.mm"
include "sylan9eq.mm"
include "ex.mm"
include "ralimdva.mm"
include "3impia.mm"
include "raleqdv.mm"
include "mpbird.mm"
include "wb.mm"
include "wne.mm"
include "simpll.mm"
include "eleq2i.mm"
include "simplr.mm"
include "nelrnfvne.mm"
include "syl3anc.mm"
include "neeq1.mm"
include "syl5ibrcom.mm"
include "fvn0ssdmfun.mm"
include "simprd.mm"
include "simp1.mm"
include "eqfunfv.mm"
include "syl2anc.mm"
include "mpbir2and.mm"

theorem fveqressseq
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let va: setvar a
  let vb: setvar b
  assume fveqdmss.1: |- D = dom B

  disjoint A x
  disjoint B x
  disjoint D x
  disjoint A a
  disjoint A b
  disjoint a b
  disjoint a x
  disjoint b x
  disjoint B a
  disjoint B b
  disjoint D a
  assert |- ( ( Fun B /\ (/) e/ ran B /\ A. x e. D ( A ` x ) = ( B ` x ) ) -> ( A |` D ) = B )

  proof
    cB
    wfun
    #
    c0
    cB
    crn
    wnel
    #
    vx
    cv
    #
    cA
    cfv
    #
    @2
    cB
    cfv
    #
    wceq
    #
    vx
    cD
    wral
    #
    w3a
    #
    cA
    cD
    cres
    #
    cB
    wceq
    #
    @8
    cdm
    #
    cB
    cdm
    #
    wceq
    #
    @2
    @8
    cfv
    #
    @4
    wceq
    #
    vx
    @10
    wral
    #
    @7
    cD
    cA
    cdm
    #
    wss
    #
    @12
    vx
    cA
    cB
    cD
    fveqdmss.1
    fveqdmss
    #
    @17
    @10
    cD
    @11
    @17
    @10
    cD
    @16
    cin
    #
    cD
    cA
    cD
    dmres
    #
    @17
    @19
    @16
    cD
    cin
    #
    cD
    cD
    @16
    incom
    @17
    @21
    cD
    wceq
    cD
    @16
    sseqin2
    biimpi
    syl5eq
    #
    syl5eq
    fveqdmss.1
    syl6eq
    syl
    @7
    @15
    @14
    vx
    cD
    wral
    #
    @0
    @1
    @6
    @23
    @0
    @1
    wa
    #
    @5
    @14
    vx
    cD
    @24
    @2
    cD
    wcel
    #
    wa
    #
    @5
    @14
    @26
    @5
    @13
    @3
    @4
    @25
    @13
    @3
    wceq
    @24
    @2
    cD
    cA
    fvres
    adantl
    @5
    id
    sylan9eq
    ex
    ralimdva
    3impia
    @7
    @14
    vx
    @10
    cD
    @7
    @10
    @19
    cD
    @20
    @7
    @17
    @19
    cD
    wceq
    @18
    @22
    syl
    syl5eq
    raleqdv
    mpbird
    @7
    @8
    wfun
    #
    @0
    @9
    @12
    @15
    wa
    wb
    @7
    @3
    c0
    wne
    #
    vx
    cD
    wral
    #
    @27
    @0
    @1
    @6
    @29
    @24
    @5
    @28
    vx
    cD
    @26
    @28
    @5
    @4
    c0
    wne
    #
    @26
    @0
    @2
    @11
    wcel
    #
    @1
    @30
    @0
    @1
    @25
    simpll
    @25
    @31
    @24
    @25
    @31
    cD
    @11
    @2
    fveqdmss.1
    eleq2i
    biimpi
    adantl
    @0
    @1
    @25
    simplr
    cB
    @2
    c0
    nelrnfvne
    syl3anc
    @3
    @4
    c0
    neeq1
    syl5ibrcom
    ralimdva
    3impia
    @29
    @17
    @27
    cD
    cA
    vx
    fvn0ssdmfun
    simprd
    syl
    @0
    @1
    @6
    simp1
    vx
    @8
    cB
    eqfunfv
    syl2anc
    mpbir2and
end

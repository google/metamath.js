include "wfun.mm"
include "crn.mm"
include "wss.mm"
include "ccnv.mm"
include "cres.mm"
include "w3a.mm"
include "cima.mm"
include "wf1o.mm"
include "wfn.mm"
include "wceq.mm"
include "cdm.mm"
include "funfn.mm"
include "biimpi.mm"
include "3ad2ant3.mm"
include "simp2.mm"
include "df-rn.mm"
include "syl6sseq.mm"
include "ssdmres.mm"
include "sylib.mm"
include "fneq2d.mm"
include "mpbid.mm"
include "simp1.mm"
include "funres.mm"
include "syl.mm"
include "funcnvres2.mm"
include "funeqd.mm"
include "mpbird.mm"
include "df-ima.mm"
include "eqcomi.mm"
include "a1i.mm"
include "3jca.mm"
include "dff1o2.mm"
include "sylibr.mm"
include "f1ocnv.mm"
include "wb.mm"
include "f1oeq1.mm"
include "3syl.mm"

theorem fresf1o
  let cC: class C
  let cF: class F


  assert |- ( ( Fun F /\ C C_ ran F /\ Fun ( `' F |` C ) ) -> ( F |` ( `' F " C ) ) : ( `' F " C ) -1-1-onto-> C )

  proof
    cF
    wfun
    #
    cC
    cF
    crn
    #
    wss
    #
    cF
    ccnv
    #
    cC
    cres
    #
    wfun
    #
    w3a
    #
    @3
    cC
    cima
    #
    cC
    @4
    ccnv
    #
    wf1o
    #
    @7
    cC
    cF
    @7
    cres
    #
    wf1o
    #
    @6
    cC
    @7
    @4
    wf1o
    #
    @9
    @6
    @4
    cC
    wfn
    #
    @8
    wfun
    #
    @4
    crn
    #
    @7
    wceq
    #
    w3a
    @12
    @6
    @13
    @14
    @16
    @6
    @4
    @4
    cdm
    #
    wfn
    #
    @13
    @5
    @0
    @18
    @2
    @5
    @18
    @4
    funfn
    biimpi
    3ad2ant3
    @6
    @17
    cC
    @4
    @6
    cC
    @3
    cdm
    #
    wss
    @17
    cC
    wceq
    @6
    cC
    @1
    @19
    @0
    @2
    @5
    simp2
    cF
    df-rn
    syl6sseq
    cC
    @3
    ssdmres
    sylib
    fneq2d
    mpbid
    @6
    @14
    @10
    wfun
    #
    @6
    @0
    @20
    @0
    @2
    @5
    simp1
    #
    @7
    cF
    funres
    syl
    @6
    @8
    @10
    @6
    @0
    @8
    @10
    wceq
    #
    @21
    cC
    cF
    funcnvres2
    #
    syl
    funeqd
    mpbird
    @16
    @6
    @7
    @15
    @3
    cC
    df-ima
    eqcomi
    a1i
    3jca
    cC
    @7
    @4
    dff1o2
    sylibr
    cC
    @7
    @4
    f1ocnv
    syl
    @6
    @0
    @22
    @9
    @11
    wb
    @21
    @23
    @7
    cC
    @8
    @10
    f1oeq1
    3syl
    mpbid
end

include "ccnv.mm"
include "wfun.mm"
include "cres.mm"
include "wf1o.mm"
include "wa.mm"
include "f1ocnv.mm"
include "adantl.mm"
include "wceq.mm"
include "wb.mm"
include "cima.mm"
include "funcnvres.mm"
include "crn.mm"
include "df-ima.mm"
include "wf1.mm"
include "dff1o5.mm"
include "simprbi.mm"
include "syl5eq.mm"
include "reseq2d.mm"
include "sylan9eq.mm"
include "f1oeq1.mm"
include "syl.mm"
include "mpbid.mm"

theorem f1orescnv
  let cP: class P
  let cR: class R
  let cF: class F


  assert |- ( ( Fun `' F /\ ( F |` R ) : R -1-1-onto-> P ) -> ( `' F |` P ) : P -1-1-onto-> R )

  proof
    cF
    ccnv
    #
    wfun
    #
    cR
    cP
    cF
    cR
    cres
    #
    wf1o
    #
    wa
    #
    cP
    cR
    @2
    ccnv
    #
    wf1o
    #
    cP
    cR
    @0
    cP
    cres
    #
    wf1o
    #
    @3
    @6
    @1
    cR
    cP
    @2
    f1ocnv
    adantl
    @4
    @5
    @7
    wceq
    @6
    @8
    wb
    @1
    @3
    @5
    @0
    cF
    cR
    cima
    #
    cres
    @7
    cR
    cF
    funcnvres
    @3
    @9
    cP
    @0
    @3
    @9
    @2
    crn
    #
    cP
    cF
    cR
    df-ima
    @3
    cR
    cP
    @2
    wf1
    @10
    cP
    wceq
    cR
    cP
    @2
    dff1o5
    simprbi
    syl5eq
    reseq2d
    sylan9eq
    cP
    cR
    @5
    @7
    f1oeq1
    syl
    mpbid
end

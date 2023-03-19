include "wf.mm"
include "wfn.mm"
include "cid.mm"
include "cres.mm"
include "ccom.mm"
include "wceq.mm"
include "ffn.mm"
include "wfun.mm"
include "cdm.mm"
include "wa.mm"
include "df-fn.mm"
include "wss.mm"
include "eqimss.mm"
include "ccnv.mm"
include "cnvi.mm"
include "reseq1i.mm"
include "cnveqi.mm"
include "cnvresid.mm"
include "eqtr2i.mm"
include "coeq2i.mm"
include "cores2.mm"
include "syl5eq.mm"
include "syl.mm"
include "wrel.mm"
include "funrel.mm"
include "coi1.mm"
include "sylan9eqr.mm"
include "sylbi.mm"

theorem fcoi1
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A --> B -> ( F o. ( _I |` A ) ) = F )

  proof
    cA
    cB
    cF
    wf
    cF
    cA
    wfn
    #
    cF
    cid
    cA
    cres
    #
    ccom
    #
    cF
    wceq
    #
    cA
    cB
    cF
    ffn
    @0
    cF
    wfun
    #
    cF
    cdm
    #
    cA
    wceq
    #
    wa
    @3
    cF
    cA
    df-fn
    @6
    @4
    @2
    cF
    cid
    ccom
    #
    cF
    @6
    @5
    cA
    wss
    #
    @2
    @7
    wceq
    @5
    cA
    eqimss
    @8
    @2
    cF
    cid
    ccnv
    #
    cA
    cres
    #
    ccnv
    #
    ccom
    @7
    @1
    @11
    cF
    @11
    @1
    ccnv
    @1
    @10
    @1
    @9
    cid
    cA
    cnvi
    reseq1i
    cnveqi
    cA
    cnvresid
    eqtr2i
    coeq2i
    cF
    cid
    cA
    cores2
    syl5eq
    syl
    @4
    cF
    wrel
    @7
    cF
    wceq
    cF
    funrel
    cF
    coi1
    syl
    sylan9eqr
    sylbi
    syl
end

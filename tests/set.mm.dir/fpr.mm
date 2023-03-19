include "wne.mm"
include "cop.mm"
include "cpr.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "wa.mm"
include "wf.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "funpr.mm"
include "dmprop.mm"
include "jctir.mm"
include "df-fn.mm"
include "sylibr.mm"
include "csn.mm"
include "cun.mm"
include "df-pr.mm"
include "rneqi.mm"
include "rnun.mm"
include "rnsnop.mm"
include "uneq12i.mm"
include "eqtr4i.mm"
include "3eqtri.mm"
include "eqimssi.mm"
include "df-f.mm"

theorem fpr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume fpr.1: |- A e. _V
  assume fpr.2: |- B e. _V
  assume fpr.3: |- C e. _V
  assume fpr.4: |- D e. _V


  assert |- ( A =/= B -> { <. A , C >. , <. B , D >. } : { A , B } --> { C , D } )

  proof
    cA
    cB
    wne
    #
    cA
    cC
    cop
    #
    cB
    cD
    cop
    #
    cpr
    #
    cA
    cB
    cpr
    #
    wfn
    #
    @3
    crn
    #
    cC
    cD
    cpr
    #
    wss
    #
    wa
    @4
    @7
    @3
    wf
    @0
    @5
    @8
    @0
    @3
    wfun
    #
    @3
    cdm
    @4
    wceq
    #
    wa
    @5
    @0
    @9
    @10
    cA
    cB
    cC
    cD
    fpr.1
    fpr.2
    fpr.3
    fpr.4
    funpr
    cA
    cC
    cB
    cD
    fpr.3
    fpr.4
    dmprop
    jctir
    @3
    @4
    df-fn
    sylibr
    @6
    @7
    @6
    @1
    csn
    #
    @2
    csn
    #
    cun
    #
    crn
    @11
    crn
    #
    @12
    crn
    #
    cun
    #
    @7
    @3
    @13
    @1
    @2
    df-pr
    rneqi
    @11
    @12
    rnun
    @16
    cC
    csn
    #
    cD
    csn
    #
    cun
    @7
    @14
    @17
    @15
    @18
    cA
    cC
    fpr.1
    rnsnop
    cB
    cD
    fpr.2
    rnsnop
    uneq12i
    cC
    cD
    df-pr
    eqtr4i
    3eqtri
    eqimssi
    jctir
    @4
    @7
    @3
    df-f
    sylibr
end

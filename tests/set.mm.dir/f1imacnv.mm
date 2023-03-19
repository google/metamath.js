include "wf1.mm"
include "wss.mm"
include "wa.mm"
include "ccnv.mm"
include "cima.mm"
include "cres.mm"
include "resima.mm"
include "wfun.mm"
include "wceq.mm"
include "wf.mm"
include "df-f1.mm"
include "simprbi.mm"
include "adantr.mm"
include "funcnvres.mm"
include "syl.mm"
include "imaeq1d.mm"
include "wf1o.mm"
include "f1ores.mm"
include "f1ocnv.mm"
include "cdm.mm"
include "crn.mm"
include "imadmrn.mm"
include "f1odm.mm"
include "imaeq2d.mm"
include "wfo.mm"
include "f1ofo.mm"
include "forn.mm"
include "3eqtr3a.mm"
include "eqtr3d.mm"
include "syl5eqr.mm"

theorem f1imacnv
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( ( F : A -1-1-> B /\ C C_ A ) -> ( `' F " ( F " C ) ) = C )

  proof
    cA
    cB
    cF
    wf1
    #
    cC
    cA
    wss
    #
    wa
    #
    cF
    ccnv
    #
    cF
    cC
    cima
    #
    cima
    @3
    @4
    cres
    #
    @4
    cima
    #
    cC
    @3
    @4
    resima
    @2
    cF
    cC
    cres
    #
    ccnv
    #
    @4
    cima
    #
    @6
    cC
    @2
    @8
    @5
    @4
    @2
    @3
    wfun
    #
    @8
    @5
    wceq
    @0
    @10
    @1
    @0
    cA
    cB
    cF
    wf
    @10
    cA
    cB
    cF
    df-f1
    simprbi
    adantr
    cC
    cF
    funcnvres
    syl
    imaeq1d
    @2
    @4
    cC
    @8
    wf1o
    #
    @9
    cC
    wceq
    @2
    cC
    @4
    @7
    wf1o
    @11
    cA
    cB
    cC
    cF
    f1ores
    cC
    @4
    @7
    f1ocnv
    syl
    @11
    @8
    @8
    cdm
    #
    cima
    @8
    crn
    #
    @9
    cC
    @8
    imadmrn
    @11
    @12
    @4
    @8
    @4
    cC
    @8
    f1odm
    imaeq2d
    @11
    @4
    cC
    @8
    wfo
    @13
    cC
    wceq
    @4
    cC
    @8
    f1ofo
    @4
    cC
    @8
    forn
    syl
    3eqtr3a
    syl
    eqtr3d
    syl5eqr
end

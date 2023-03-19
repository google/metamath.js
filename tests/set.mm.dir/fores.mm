include "wfun.mm"
include "cdm.mm"
include "wss.mm"
include "wa.mm"
include "cres.mm"
include "cima.mm"
include "wfo.mm"
include "funres.mm"
include "anim1i.mm"
include "wfn.mm"
include "wceq.mm"
include "df-fn.mm"
include "crn.mm"
include "df-ima.mm"
include "eqcomi.mm"
include "df-fo.mm"
include "mpbiran2.mm"
include "ssdmres.mm"
include "anbi2i.mm"
include "3bitr4i.mm"
include "sylibr.mm"

theorem fores
  let cA: class A
  let cF: class F


  assert |- ( ( Fun F /\ A C_ dom F ) -> ( F |` A ) : A -onto-> ( F " A ) )

  proof
    cF
    wfun
    #
    cA
    cF
    cdm
    wss
    #
    wa
    cF
    cA
    cres
    #
    wfun
    #
    @1
    wa
    #
    cA
    cF
    cA
    cima
    #
    @2
    wfo
    #
    @0
    @3
    @1
    cA
    cF
    funres
    anim1i
    @2
    cA
    wfn
    #
    @3
    @2
    cdm
    cA
    wceq
    #
    wa
    @6
    @4
    @2
    cA
    df-fn
    @6
    @7
    @2
    crn
    #
    @5
    wceq
    @5
    @9
    cF
    cA
    df-ima
    eqcomi
    cA
    @5
    @2
    df-fo
    mpbiran2
    @1
    @8
    @3
    cA
    cF
    ssdmres
    anbi2i
    3bitr4i
    sylibr
end

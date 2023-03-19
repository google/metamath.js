include "wfun.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cafv.mm"
include "crn.mm"
include "wdfat.mm"
include "wceq.mm"
include "csn.mm"
include "cres.mm"
include "funres.mm"
include "anim1i.mm"
include "ancomd.mm"
include "df-dfat.mm"
include "sylibr.mm"
include "afvfundmfveq.mm"
include "eqcomd.mm"
include "syl.mm"
include "fvelrn.mm"
include "eqeltrrd.mm"

theorem afvelrn
  let cA: class A
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( Fun F /\ A e. dom F ) -> ( F ''' A ) e. ran F )

  proof
    cF
    wfun
    #
    cA
    cF
    cdm
    wcel
    #
    wa
    #
    cA
    cF
    cfv
    #
    cA
    cF
    cafv
    #
    cF
    crn
    @2
    cA
    cF
    wdfat
    #
    @3
    @4
    wceq
    @2
    @1
    cF
    cA
    csn
    #
    cres
    wfun
    #
    wa
    @5
    @2
    @7
    @1
    @0
    @7
    @1
    @6
    cF
    funres
    anim1i
    ancomd
    cA
    cF
    df-dfat
    sylibr
    @5
    @4
    @3
    cA
    cF
    afvfundmfveq
    eqcomd
    syl
    cA
    cF
    fvelrn
    eqeltrrd
end

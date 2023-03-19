include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "wdfat.mm"
include "cafv.mm"
include "wceq.mm"
include "cdm.mm"
include "wcel.mm"
include "csn.mm"
include "cres.mm"
include "wfun.mm"
include "wa.mm"
include "fvfundmfvn0.mm"
include "df-dfat.mm"
include "sylibr.mm"
include "afvfundmfveq.mm"
include "syl.mm"

theorem afvfvn0fveq
  let cA: class A
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( F ` A ) =/= (/) -> ( F ''' A ) = ( F ` A ) )

  proof
    cA
    cF
    cfv
    #
    c0
    wne
    #
    cA
    cF
    wdfat
    #
    cA
    cF
    cafv
    @0
    wceq
    @1
    cA
    cF
    cdm
    wcel
    cF
    cA
    csn
    cres
    wfun
    wa
    @2
    cA
    cF
    fvfundmfvn0
    cA
    cF
    df-dfat
    sylibr
    cA
    cF
    afvfundmfveq
    syl
end

include "co.mm"
include "c0.mm"
include "wne.mm"
include "cop.mm"
include "cfv.mm"
include "cdm.mm"
include "wcel.mm"
include "csn.mm"
include "cres.mm"
include "wfun.mm"
include "wa.mm"
include "df-ov.mm"
include "neeq1i.mm"
include "fvfundmfvn0.mm"
include "sylbi.mm"

theorem ovn0dmfun
  let cA: class A
  let cB: class B
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A F B ) =/= (/) -> ( <. A , B >. e. dom F /\ Fun ( F |` { <. A , B >. } ) ) )

  proof
    cA
    cB
    cF
    co
    #
    c0
    wne
    cA
    cB
    cop
    #
    cF
    cfv
    #
    c0
    wne
    @1
    cF
    cdm
    wcel
    cF
    @1
    csn
    cres
    wfun
    wa
    @0
    @2
    c0
    cA
    cB
    cF
    df-ov
    neeq1i
    @1
    cF
    fvfundmfvn0
    sylbi
end

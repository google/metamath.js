include "cdm.mm"
include "wcel.mm"
include "wn.mm"
include "wdfat.mm"
include "cafv.mm"
include "cvv.mm"
include "wceq.mm"
include "csn.mm"
include "cres.mm"
include "wfun.mm"
include "df-dfat.mm"
include "simplbi.mm"
include "con3i.mm"
include "afvnfundmuv.mm"
include "syl.mm"

theorem ndmafv
  let cA: class A
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( -. A e. dom F -> ( F ''' A ) = _V )

  proof
    cA
    cF
    cdm
    wcel
    #
    wn
    cA
    cF
    wdfat
    #
    wn
    cA
    cF
    cafv
    cvv
    wceq
    @1
    @0
    @1
    @0
    cF
    cA
    csn
    cres
    wfun
    cA
    cF
    df-dfat
    simplbi
    con3i
    cA
    cF
    afvnfundmuv
    syl
end

include "csn.mm"
include "cres.mm"
include "wfun.mm"
include "wn.mm"
include "wdfat.mm"
include "cafv.mm"
include "cvv.mm"
include "wceq.mm"
include "cdm.mm"
include "wcel.mm"
include "df-dfat.mm"
include "simprbi.mm"
include "con3i.mm"
include "afvnfundmuv.mm"
include "syl.mm"

theorem nfunsnafv
  let cA: class A
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( -. Fun ( F |` { A } ) -> ( F ''' A ) = _V )

  proof
    cF
    cA
    csn
    cres
    wfun
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
    cA
    cF
    cdm
    wcel
    @0
    cA
    cF
    df-dfat
    simprbi
    con3i
    cA
    cF
    afvnfundmuv
    syl
end

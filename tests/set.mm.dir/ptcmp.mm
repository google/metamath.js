include "wcel.mm"
include "ccmp.mm"
include "wf.mm"
include "cpt.mm"
include "cfv.mm"
include "cuni.mm"
include "cufl.mm"
include "ccrd.mm"
include "cdm.mm"
include "cin.mm"
include "cvv.mm"
include "fvex.mm"
include "uniex.mm"
include "wac.mm"
include "wceq.mm"
include "axac3.mm"
include "acufl.mm"
include "ax-mp.mm"
include "eleqtrri.mm"
include "cardeqv.mm"
include "elin.mm"
include "mpbir2an.mm"
include "eqid.mm"
include "ptcmpg.mm"
include "mp3an3.mm"

theorem ptcmp
  let cA: class A
  let cF: class F
  let cV: class V


  assert |- ( ( A e. V /\ F : A --> Comp ) -> ( Xt_ ` F ) e. Comp )

  proof
    cA
    cV
    wcel
    cA
    ccmp
    cF
    wf
    cF
    cpt
    cfv
    #
    cuni
    #
    cufl
    ccrd
    cdm
    #
    cin
    wcel
    #
    @0
    ccmp
    wcel
    @3
    @1
    cufl
    wcel
    @1
    @2
    wcel
    @1
    cvv
    cufl
    @0
    cF
    cpt
    fvex
    uniex
    #
    wac
    cufl
    cvv
    wceq
    axac3
    acufl
    ax-mp
    eleqtrri
    @1
    cvv
    @2
    @4
    cardeqv
    eleqtrri
    @1
    cufl
    @2
    elin
    mpbir2an
    cA
    cF
    @0
    cV
    @1
    @0
    eqid
    @1
    eqid
    ptcmpg
    mp3an3
end

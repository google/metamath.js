include "wfun.mm"
include "wcel.mm"
include "cima.mm"
include "cvv.mm"
include "cwdom.mm"
include "wbr.mm"
include "funimaexg.mm"
include "wdomima2g.mm"
include "mpd3an3.mm"

theorem wdomimag
  let cA: class A
  let cF: class F
  let cV: class V


  assert |- ( ( Fun F /\ A e. V ) -> ( F " A ) ~<_* A )

  proof
    cF
    wfun
    cA
    cV
    wcel
    cF
    cA
    cima
    #
    cvv
    wcel
    @0
    cA
    cwdom
    wbr
    cF
    cA
    cV
    funimaexg
    cA
    cF
    cV
    cvv
    wdomima2g
    mpd3an3
end

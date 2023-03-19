include "wcel.mm"
include "cep.mm"
include "ccnv.mm"
include "cres.mm"
include "cvv.mm"
include "cxrn.mm"
include "cnvepresex.mm"
include "adantr.mm"
include "xrnresex.mm"
include "mpd3an3.mm"

theorem xrncnvepresex
  let cA: class A
  let cR: class R
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ R e. W ) -> ( R |X. ( `' _E |` A ) ) e. _V )

  proof
    cA
    cV
    wcel
    #
    cR
    cW
    wcel
    #
    cep
    ccnv
    #
    cA
    cres
    #
    cvv
    wcel
    #
    cR
    @3
    cxrn
    cvv
    wcel
    @0
    @4
    @1
    cA
    cV
    cnvepresex
    adantr
    cA
    cR
    @2
    cV
    cW
    cvv
    xrnresex
    mpd3an3
end

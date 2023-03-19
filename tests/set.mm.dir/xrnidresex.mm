include "wcel.mm"
include "cid.mm"
include "cres.mm"
include "cvv.mm"
include "cxrn.mm"
include "resiexg.mm"
include "adantr.mm"
include "xrnresex.mm"
include "mpd3an3.mm"

theorem xrnidresex
  let cA: class A
  let cR: class R
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ R e. W ) -> ( R |X. ( _I |` A ) ) e. _V )

  proof
    cA
    cV
    wcel
    #
    cR
    cW
    wcel
    #
    cid
    cA
    cres
    #
    cvv
    wcel
    #
    cR
    @2
    cxrn
    cvv
    wcel
    @0
    @3
    @1
    cA
    cV
    resiexg
    adantr
    cA
    cR
    cid
    cV
    cW
    cvv
    xrnresex
    mpd3an3
end

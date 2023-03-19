include "c0.mm"
include "wpss.mm"
include "wss.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "0ss.mm"
include "a1i.mm"
include "iman.mm"
include "mpbi.mm"
include "dfpss3.mm"
include "mtbir.mm"

theorem npss0OLD
  let cA: class A


  assert |- -. A C. (/)

  proof
    cA
    c0
    wpss
    cA
    c0
    wss
    #
    c0
    cA
    wss
    #
    wn
    wa
    #
    @0
    @1
    wi
    @2
    wn
    @1
    @0
    cA
    0ss
    a1i
    @0
    @1
    iman
    mpbi
    cA
    c0
    dfpss3
    mtbir
end

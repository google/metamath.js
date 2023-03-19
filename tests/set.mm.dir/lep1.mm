include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "ltp1.mm"
include "wi.mm"
include "peano2re.mm"
include "ltle.mm"
include "mpdan.mm"
include "mpd.mm"

theorem lep1
  let cA: class A


  assert |- ( A e. RR -> A <_ ( A + 1 ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cA
    c1
    caddc
    co
    #
    clt
    wbr
    #
    cA
    @1
    cle
    wbr
    #
    cA
    ltp1
    @0
    @1
    cr
    wcel
    @2
    @3
    wi
    cA
    peano2re
    cA
    @1
    ltle
    mpdan
    mpd
end

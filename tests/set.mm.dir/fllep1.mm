include "cr.mm"
include "wcel.mm"
include "cfl.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "flltp1.mm"
include "wi.mm"
include "reflcl.mm"
include "peano2re.mm"
include "syl.mm"
include "ltle.mm"
include "mpdan.mm"
include "mpd.mm"

theorem fllep1
  let cA: class A


  assert |- ( A e. RR -> A <_ ( ( |_ ` A ) + 1 ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cA
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    clt
    wbr
    #
    cA
    @2
    cle
    wbr
    #
    cA
    flltp1
    @0
    @2
    cr
    wcel
    #
    @3
    @4
    wi
    @0
    @1
    cr
    wcel
    @5
    cA
    reflcl
    @1
    peano2re
    syl
    cA
    @2
    ltle
    mpdan
    mpd
end

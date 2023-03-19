include "cr.mm"
include "wcel.mm"
include "cfl.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "fraclt1.mm"
include "wi.mm"
include "reflcl.mm"
include "resubcl.mm"
include "mpdan.mm"
include "1re.mm"
include "ltle.mm"
include "sylancl.mm"
include "mpd.mm"

theorem fracle1
  let cA: class A


  assert |- ( A e. RR -> ( A - ( |_ ` A ) ) <_ 1 )

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
    cmin
    co
    #
    c1
    clt
    wbr
    #
    @2
    c1
    cle
    wbr
    #
    cA
    fraclt1
    @0
    @2
    cr
    wcel
    #
    c1
    cr
    wcel
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
    cA
    @1
    resubcl
    mpdan
    1re
    @2
    c1
    ltle
    sylancl
    mpd
end

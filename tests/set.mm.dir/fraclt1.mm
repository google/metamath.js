include "cr.mm"
include "wcel.mm"
include "cfl.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "flltp1.mm"
include "wb.mm"
include "reflcl.mm"
include "1re.mm"
include "ltsubadd2.mm"
include "mp3an3.mm"
include "mpdan.mm"
include "mpbird.mm"

theorem fraclt1
  let cA: class A


  assert |- ( A e. RR -> ( A - ( |_ ` A ) ) < 1 )

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
    c1
    clt
    wbr
    #
    cA
    @1
    c1
    caddc
    co
    clt
    wbr
    #
    cA
    flltp1
    @0
    @1
    cr
    wcel
    #
    @2
    @3
    wb
    #
    cA
    reflcl
    @0
    @4
    c1
    cr
    wcel
    @5
    1re
    cA
    @1
    c1
    ltsubadd2
    mp3an3
    mpdan
    mpbird
end

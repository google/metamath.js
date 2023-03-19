include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cfl.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "flle.mm"
include "wb.mm"
include "reflcl.mm"
include "subge0.mm"
include "mpdan.mm"
include "mpbird.mm"

theorem fracge0
  let cA: class A


  assert |- ( A e. RR -> 0 <_ ( A - ( |_ ` A ) ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cA
    cfl
    cfv
    #
    cmin
    co
    cle
    wbr
    #
    @1
    cA
    cle
    wbr
    #
    cA
    flle
    @0
    @1
    cr
    wcel
    @2
    @3
    wb
    cA
    reflcl
    cA
    @1
    subge0
    mpdan
    mpbird
end

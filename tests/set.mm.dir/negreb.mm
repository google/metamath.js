include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "cr.mm"
include "renegcl.mm"
include "negneg.mm"
include "eleq1d.mm"
include "syl5ib.mm"
include "impbid1.mm"

theorem negreb
  let cA: class A


  assert |- ( A e. CC -> ( -u A e. RR <-> A e. RR ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cneg
    #
    cr
    wcel
    #
    cA
    cr
    wcel
    #
    @2
    @1
    cneg
    #
    cr
    wcel
    @0
    @3
    @1
    renegcl
    @0
    @4
    cA
    cr
    cA
    negneg
    eleq1d
    syl5ib
    cA
    renegcl
    impbid1
end

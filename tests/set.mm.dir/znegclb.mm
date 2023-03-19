include "cc.mm"
include "wcel.mm"
include "cz.mm"
include "cneg.mm"
include "znegcl.mm"
include "negneg.mm"
include "eleq1d.mm"
include "syl5ib.mm"
include "impbid2.mm"

theorem znegclb
  let cA: class A


  assert |- ( A e. CC -> ( A e. ZZ <-> -u A e. ZZ ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cz
    wcel
    #
    cA
    cneg
    #
    cz
    wcel
    #
    cA
    znegcl
    @3
    @2
    cneg
    #
    cz
    wcel
    @0
    @1
    @2
    znegcl
    @0
    @4
    cA
    cz
    cA
    negneg
    eleq1d
    syl5ib
    impbid2
end

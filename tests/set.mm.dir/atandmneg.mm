include "catan.mm"
include "cdm.mm"
include "wcel.mm"
include "cneg.mm"
include "cc.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "wne.mm"
include "atandm3.mm"
include "simplbi.mm"
include "negcld.mm"
include "wceq.mm"
include "sqneg.mm"
include "syl.mm"
include "simprbi.mm"
include "eqnetrd.mm"
include "sylanbrc.mm"

theorem atandmneg
  let cA: class A


  assert |- ( A e. dom arctan -> -u A e. dom arctan )

  proof
    cA
    catan
    cdm
    #
    wcel
    #
    cA
    cneg
    #
    cc
    wcel
    @2
    c2
    cexp
    co
    #
    c1
    cneg
    #
    wne
    @2
    @0
    wcel
    @1
    cA
    @1
    cA
    cc
    wcel
    #
    cA
    c2
    cexp
    co
    #
    @4
    wne
    #
    cA
    atandm3
    #
    simplbi
    #
    negcld
    @1
    @3
    @6
    @4
    @1
    @5
    @3
    @6
    wceq
    @9
    cA
    sqneg
    syl
    @1
    @5
    @7
    @8
    simprbi
    eqnetrd
    @2
    atandm3
    sylanbrc
end

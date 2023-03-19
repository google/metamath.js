include "cvv.mm"
include "wcel.mm"
include "bj-csngl.mm"
include "c0.mm"
include "csn.mm"
include "wa.mm"
include "cun.mm"
include "bj-ctag.mm"
include "bj-snglex.mm"
include "p0ex.mm"
include "biantru.mm"
include "bitri.mm"
include "unexb.mm"
include "df-bj-tag.mm"
include "eqcomi.mm"
include "eleq1i.mm"
include "3bitri.mm"

theorem bj-tagex
  let cA: class A


  assert |- ( A e. _V <-> tag A e. _V )

  proof
    cA
    cvv
    wcel
    #
    cA
    bj-csngl
    #
    cvv
    wcel
    #
    c0
    csn
    #
    cvv
    wcel
    #
    wa
    #
    @1
    @3
    cun
    #
    cvv
    wcel
    cA
    bj-ctag
    #
    cvv
    wcel
    @0
    @2
    @5
    cA
    bj-snglex
    @4
    @2
    p0ex
    biantru
    bitri
    @1
    @3
    unexb
    @6
    @7
    cvv
    @7
    @6
    cA
    df-bj-tag
    eqcomi
    eleq1i
    3bitri
end

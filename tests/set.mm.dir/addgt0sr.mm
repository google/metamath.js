include "c0r.mm"
include "cltr.mm"
include "wbr.mm"
include "cplr.mm"
include "co.mm"
include "cnr.mm"
include "wcel.mm"
include "wb.mm"
include "ltrelsr.mm"
include "brel.mm"
include "simprd.mm"
include "ltasr.mm"
include "0idsr.mm"
include "breq1d.mm"
include "bitrd.mm"
include "syl.mm"
include "biimpa.mm"
include "ltsosr.mm"
include "sotri.mm"
include "syldan.mm"

theorem addgt0sr
  let cA: class A
  let cB: class B


  assert |- ( ( 0R <R A /\ 0R <R B ) -> 0R <R ( A +R B ) )

  proof
    c0r
    cA
    cltr
    wbr
    #
    c0r
    cB
    cltr
    wbr
    #
    cA
    cA
    cB
    cplr
    co
    #
    cltr
    wbr
    #
    c0r
    @2
    cltr
    wbr
    @0
    @1
    @3
    @0
    cA
    cnr
    wcel
    #
    @1
    @3
    wb
    @0
    c0r
    cnr
    wcel
    @4
    c0r
    cA
    cnr
    cnr
    cltr
    ltrelsr
    brel
    simprd
    @4
    @1
    cA
    c0r
    cplr
    co
    #
    @2
    cltr
    wbr
    @3
    c0r
    cB
    cA
    ltasr
    @4
    @5
    cA
    @2
    cltr
    cA
    0idsr
    breq1d
    bitrd
    syl
    biimpa
    c0r
    cA
    @2
    cltr
    cnr
    ltsosr
    ltrelsr
    sotri
    syldan
end

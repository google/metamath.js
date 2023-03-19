include "wbr.mm"
include "wcel.mm"
include "wn.mm"
include "wi.mm"
include "brel.mm"
include "simpld.mm"
include "wa.mm"
include "wceq.mm"
include "wo.mm"
include "wor.mm"
include "wb.mm"
include "sotric.mm"
include "mpan.mm"
include "con2bid.mm"
include "breq1.mm"
include "biimpd.mm"
include "sotri.mm"
include "ex.mm"
include "jaoi.mm"
include "syl6bir.mm"
include "com3r.mm"
include "mpand.mm"
include "3imp231.mm"

theorem sotri2
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  assume soi.1: |- R Or S
  assume soi.2: |- R C_ ( S X. S )


  assert |- ( ( A e. S /\ -. B R A /\ B R C ) -> A R C )

  proof
    cB
    cC
    cR
    wbr
    #
    cA
    cS
    wcel
    #
    cB
    cA
    cR
    wbr
    #
    wn
    #
    cA
    cC
    cR
    wbr
    #
    @0
    cB
    cS
    wcel
    #
    @1
    @3
    @4
    wi
    @0
    @5
    cC
    cS
    wcel
    cB
    cC
    cS
    cS
    cR
    soi.2
    brel
    simpld
    @5
    @1
    wa
    #
    @3
    @0
    @4
    @6
    @3
    cB
    cA
    wceq
    #
    cA
    cB
    cR
    wbr
    #
    wo
    #
    @0
    @4
    wi
    #
    @6
    @2
    @9
    cS
    cR
    wor
    @6
    @2
    @9
    wn
    wb
    soi.1
    cS
    cB
    cA
    cR
    sotric
    mpan
    con2bid
    @7
    @10
    @8
    @7
    @0
    @4
    cB
    cA
    cC
    cR
    breq1
    biimpd
    @8
    @0
    @4
    cA
    cB
    cC
    cR
    cS
    soi.1
    soi.2
    sotri
    ex
    jaoi
    syl6bir
    com3r
    mpand
    3imp231
end

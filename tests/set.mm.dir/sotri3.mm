include "wbr.mm"
include "wcel.mm"
include "wn.mm"
include "wi.mm"
include "brel.mm"
include "simprd.mm"
include "wa.mm"
include "wceq.mm"
include "wo.mm"
include "wor.mm"
include "wb.mm"
include "sotric.mm"
include "mpan.mm"
include "con2bid.mm"
include "breq2.mm"
include "biimprd.mm"
include "sotri.mm"
include "expcom.mm"
include "jaoi.mm"
include "syl6bir.mm"
include "com3r.mm"
include "mpan2d.mm"
include "3imp21.mm"

theorem sotri3
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  assume soi.1: |- R Or S
  assume soi.2: |- R C_ ( S X. S )


  assert |- ( ( C e. S /\ A R B /\ -. C R B ) -> A R C )

  proof
    cA
    cB
    cR
    wbr
    #
    cC
    cS
    wcel
    #
    cC
    cB
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
    @1
    cB
    cS
    wcel
    #
    @3
    @4
    wi
    @0
    cA
    cS
    wcel
    @5
    cA
    cB
    cS
    cS
    cR
    soi.2
    brel
    simprd
    @1
    @5
    wa
    #
    @3
    @0
    @4
    @6
    @3
    cC
    cB
    wceq
    #
    cB
    cC
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
    cC
    cB
    cR
    sotric
    mpan
    con2bid
    @7
    @10
    @8
    @7
    @4
    @0
    cC
    cB
    cA
    cR
    breq2
    biimprd
    @0
    @8
    @4
    cA
    cB
    cC
    cR
    cS
    soi.1
    soi.2
    sotri
    expcom
    jaoi
    syl6bir
    com3r
    mpan2d
    3imp21
end

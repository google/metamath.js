include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "brel.mm"
include "simpld.mm"
include "anim12i.mm"
include "wi.mm"
include "wor.mm"
include "w3a.mm"
include "sotr.mm"
include "mpan.mm"
include "3expb.mm"
include "mpcom.mm"

theorem sotri
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  assume soi.1: |- R Or S
  assume soi.2: |- R C_ ( S X. S )


  assert |- ( ( A R B /\ B R C ) -> A R C )

  proof
    cA
    cS
    wcel
    #
    cB
    cS
    wcel
    #
    cC
    cS
    wcel
    #
    wa
    #
    wa
    cA
    cB
    cR
    wbr
    #
    cB
    cC
    cR
    wbr
    #
    wa
    #
    cA
    cC
    cR
    wbr
    #
    @4
    @0
    @5
    @3
    @4
    @0
    @1
    cA
    cB
    cS
    cS
    cR
    soi.2
    brel
    simpld
    cB
    cC
    cS
    cS
    cR
    soi.2
    brel
    anim12i
    @0
    @1
    @2
    @6
    @7
    wi
    #
    cS
    cR
    wor
    @0
    @1
    @2
    w3a
    @8
    soi.1
    cS
    cA
    cB
    cC
    cR
    sotr
    mpan
    3expb
    mpcom
end

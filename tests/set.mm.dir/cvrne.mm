include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "cplt.mm"
include "cfv.mm"
include "wne.mm"
include "eqid.mm"
include "cvrlt.mm"
include "cple.mm"
include "pltval.mm"
include "simplbda.mm"
include "syldan.mm"

theorem cvrne
  let cA: class A
  let cB: class B
  let cC: class C
  let cK: class K
  let cX: class X
  let cY: class Y
  assume cvrne.b: |- B = ( Base ` K )
  assume cvrne.c: |- C = ( <o ` K )


  assert |- ( ( ( K e. A /\ X e. B /\ Y e. B ) /\ X C Y ) -> X =/= Y )

  proof
    cK
    cA
    wcel
    cX
    cB
    wcel
    cY
    cB
    wcel
    w3a
    #
    cX
    cY
    cC
    wbr
    cX
    cY
    cK
    cplt
    cfv
    #
    wbr
    #
    cX
    cY
    wne
    #
    cA
    cB
    cC
    @1
    cK
    cX
    cY
    cvrne.b
    @1
    eqid
    #
    cvrne.c
    cvrlt
    @0
    @2
    cX
    cY
    cK
    cple
    cfv
    #
    wbr
    @3
    cA
    cB
    cB
    @1
    cK
    @5
    cX
    cY
    @5
    eqid
    @4
    pltval
    simplbda
    syldan
end

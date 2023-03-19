include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "cplt.mm"
include "cfv.mm"
include "eqid.mm"
include "cvrlt.mm"
include "wne.mm"
include "pltval.mm"
include "simprbda.mm"
include "syldan.mm"

theorem cvrle
  let cA: class A
  let cB: class B
  let cC: class C
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  assume cvrle.b: |- B = ( Base ` K )
  assume cvrle.l: |- .<_ = ( le ` K )
  assume cvrle.c: |- C = ( <o ` K )


  assert |- ( ( ( K e. A /\ X e. B /\ Y e. B ) /\ X C Y ) -> X .<_ Y )

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
    c.le
    wbr
    #
    cA
    cB
    cC
    @1
    cK
    cX
    cY
    cvrle.b
    @1
    eqid
    #
    cvrle.c
    cvrlt
    @0
    @2
    @3
    cX
    cY
    wne
    cA
    cB
    cB
    @1
    cK
    c.le
    cX
    cY
    cvrle.l
    @4
    pltval
    simprbda
    syldan
end

include "cpo.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "cplt.mm"
include "cfv.mm"
include "wn.mm"
include "eqid.mm"
include "cvrlt.mm"
include "pltnle.mm"
include "syldan.mm"

theorem cvrnle
  let cB: class B
  let cC: class C
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  assume cvrle.b: |- B = ( Base ` K )
  assume cvrle.l: |- .<_ = ( le ` K )
  assume cvrle.c: |- C = ( <o ` K )


  assert |- ( ( ( K e. Poset /\ X e. B /\ Y e. B ) /\ X C Y ) -> -. Y .<_ X )

  proof
    cK
    cpo
    wcel
    cX
    cB
    wcel
    cY
    cB
    wcel
    w3a
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
    cY
    cX
    c.le
    wbr
    wn
    cpo
    cB
    cC
    @0
    cK
    cX
    cY
    cvrle.b
    @0
    eqid
    #
    cvrle.c
    cvrlt
    cB
    @0
    cK
    c.le
    cX
    cY
    cvrle.b
    cvrle.l
    @1
    pltnle
    syldan
end

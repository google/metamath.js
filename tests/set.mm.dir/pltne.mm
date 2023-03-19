include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wne.mm"
include "cple.mm"
include "cfv.mm"
include "eqid.mm"
include "pltval.mm"
include "simplbda.mm"
include "ex.mm"

theorem pltne
  let cA: class A
  let cB: class B
  let cC: class C
  let c.lt: class .<
  let cK: class K
  let cX: class X
  let cY: class Y
  assume pltne.s: |- .< = ( lt ` K )


  assert |- ( ( K e. A /\ X e. B /\ Y e. C ) -> ( X .< Y -> X =/= Y ) )

  proof
    cK
    cA
    wcel
    cX
    cB
    wcel
    cY
    cC
    wcel
    w3a
    #
    cX
    cY
    c.lt
    wbr
    #
    cX
    cY
    wne
    #
    @0
    @1
    cX
    cY
    cK
    cple
    cfv
    #
    wbr
    @2
    cA
    cB
    cC
    c.lt
    cK
    @3
    cX
    cY
    @3
    eqid
    pltne.s
    pltval
    simplbda
    ex
end

include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wne.mm"
include "pltval.mm"
include "simprbda.mm"
include "ex.mm"

theorem pltle
  let cA: class A
  let cB: class B
  let cC: class C
  let c.lt: class .<
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume pltval.l: |- .<_ = ( le ` K )
  assume pltval.s: |- .< = ( lt ` K )


  assert |- ( ( K e. A /\ X e. B /\ Y e. C ) -> ( X .< Y -> X .<_ Y ) )

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
    c.le
    wbr
    #
    @0
    @1
    @2
    cX
    cY
    wne
    cA
    cB
    cC
    c.lt
    cK
    c.le
    cX
    cY
    pltval.l
    pltval.s
    pltval
    simprbda
    ex
end

include "chlt.mm"
include "wcel.mm"
include "clat.mm"
include "co.mm"
include "hllat.mm"
include "atbase.mm"
include "latjcl.mm"
include "syl3an.mm"

theorem hlatjcl
  let cA: class A
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let cX: class X
  let cY: class Y
  assume hlatjcl.b: |- B = ( Base ` K )
  assume hlatjcl.j: |- .\/ = ( join ` K )
  assume hlatjcl.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ X e. A /\ Y e. A ) -> ( X .\/ Y ) e. B )

  proof
    cK
    chlt
    wcel
    cK
    clat
    wcel
    cX
    cA
    wcel
    cX
    cB
    wcel
    cY
    cA
    wcel
    cY
    cB
    wcel
    cX
    cY
    c.or
    co
    cB
    wcel
    cK
    hllat
    cA
    cB
    cX
    cK
    hlatjcl.b
    hlatjcl.a
    atbase
    cA
    cB
    cY
    cK
    hlatjcl.b
    hlatjcl.a
    atbase
    cB
    c.or
    cK
    cX
    cY
    hlatjcl.b
    hlatjcl.j
    latjcl
    syl3an
end

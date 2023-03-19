include "chlt.mm"
include "wcel.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "hllat.mm"
include "eqid.mm"
include "atbase.mm"
include "latjcom.mm"
include "syl3an.mm"

theorem hlatjcom
  let cA: class A
  let c.or: class .\/
  let cK: class K
  let cX: class X
  let cY: class Y
  assume hlatjcom.j: |- .\/ = ( join ` K )
  assume hlatjcom.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ X e. A /\ Y e. A ) -> ( X .\/ Y ) = ( Y .\/ X ) )

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
    cK
    cbs
    cfv
    #
    wcel
    cY
    cA
    wcel
    cY
    @0
    wcel
    cX
    cY
    c.or
    co
    cY
    cX
    c.or
    co
    wceq
    cK
    hllat
    cA
    @0
    cX
    cK
    @0
    eqid
    #
    hlatjcom.a
    atbase
    cA
    @0
    cY
    cK
    @1
    hlatjcom.a
    atbase
    @0
    c.or
    cK
    cX
    cY
    @1
    hlatjcom.j
    latjcom
    syl3an
end

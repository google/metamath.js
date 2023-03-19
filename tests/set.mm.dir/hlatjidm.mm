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
include "latjidm.mm"
include "syl2an.mm"

theorem hlatjidm
  let cA: class A
  let c.or: class .\/
  let cK: class K
  let cX: class X
  assume hlatjcom.j: |- .\/ = ( join ` K )
  assume hlatjcom.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ X e. A ) -> ( X .\/ X ) = X )

  proof
    cK
    chlt
    wcel
    cK
    clat
    wcel
    cX
    cK
    cbs
    cfv
    #
    wcel
    cX
    cX
    c.or
    co
    cX
    wceq
    cX
    cA
    wcel
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
    @0
    c.or
    cK
    cX
    @1
    hlatjcom.j
    latjidm
    syl2an
end

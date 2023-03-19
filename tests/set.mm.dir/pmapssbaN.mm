include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "catm.mm"
include "eqid.mm"
include "pmapssat.mm"
include "atssbase.mm"
include "syl6ss.mm"

theorem pmapssbaN
  let cB: class B
  let cC: class C
  let cK: class K
  let cM: class M
  let cX: class X
  assume pmapssba.b: |- B = ( Base ` K )
  assume pmapssba.m: |- M = ( pmap ` K )


  assert |- ( ( K e. C /\ X e. B ) -> ( M ` X ) C_ B )

  proof
    cK
    cC
    wcel
    cX
    cB
    wcel
    wa
    cX
    cM
    cfv
    cK
    catm
    cfv
    #
    cB
    @0
    cB
    cC
    cK
    cM
    cX
    pmapssba.b
    @0
    eqid
    #
    pmapssba.m
    pmapssat
    @0
    cB
    cK
    pmapssba.b
    @1
    atssbase
    syl6ss
end

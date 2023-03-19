include "cdlat.mm"
include "wcel.mm"
include "codu.mm"
include "cfv.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "odudlatb.mm"
include "ibi.mm"
include "odubas.mm"
include "odujoin.mm"
include "odumeet.mm"
include "dlatmjdi.mm"
include "sylan.mm"

theorem dlatjmdi
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume dlatjmdi.b: |- B = ( Base ` K )
  assume dlatjmdi.j: |- .\/ = ( join ` K )
  assume dlatjmdi.m: |- ./\ = ( meet ` K )


  assert |- ( ( K e. DLat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( X .\/ ( Y ./\ Z ) ) = ( ( X .\/ Y ) ./\ ( X .\/ Z ) ) )

  proof
    cK
    cdlat
    wcel
    #
    cK
    codu
    cfv
    #
    cdlat
    wcel
    #
    cX
    cB
    wcel
    cY
    cB
    wcel
    cZ
    cB
    wcel
    w3a
    cX
    cY
    cZ
    c.an
    co
    c.or
    co
    cX
    cY
    c.or
    co
    cX
    cZ
    c.or
    co
    c.an
    co
    wceq
    @0
    @2
    @1
    cK
    cdlat
    @1
    eqid
    #
    odudlatb
    ibi
    cB
    c.an
    @1
    c.or
    cX
    cY
    cZ
    cB
    @1
    cK
    @3
    dlatjmdi.b
    odubas
    @1
    c.an
    cK
    @3
    dlatjmdi.m
    odujoin
    @1
    c.or
    cK
    @3
    dlatjmdi.j
    odumeet
    dlatmjdi
    sylan
end

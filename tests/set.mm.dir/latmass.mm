include "clat.mm"
include "wcel.mm"
include "codu.mm"
include "cfv.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "odulat.mm"
include "odubas.mm"
include "odujoin.mm"
include "latjass.mm"
include "sylan.mm"

theorem latmass
  let cB: class B
  let cK: class K
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume latmass.b: |- B = ( Base ` K )
  assume latmass.m: |- ./\ = ( meet ` K )


  assert |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X ./\ Y ) ./\ Z ) = ( X ./\ ( Y ./\ Z ) ) )

  proof
    cK
    clat
    wcel
    cK
    codu
    cfv
    #
    clat
    wcel
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
    c.an
    co
    cZ
    c.an
    co
    cX
    cY
    cZ
    c.an
    co
    c.an
    co
    wceq
    @0
    cK
    @0
    eqid
    #
    odulat
    cB
    c.an
    @0
    cX
    cY
    cZ
    cB
    @0
    cK
    @1
    latmass.b
    odubas
    @0
    c.an
    cK
    @1
    latmass.m
    odujoin
    latjass
    sylan
end

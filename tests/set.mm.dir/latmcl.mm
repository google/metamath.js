include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "cjn.mm"
include "cfv.mm"
include "co.mm"
include "eqid.mm"
include "latlem.mm"
include "simprd.mm"

theorem latmcl
  let cB: class B
  let cK: class K
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  assume latmcl.b: |- B = ( Base ` K )
  assume latmcl.m: |- ./\ = ( meet ` K )


  assert |- ( ( K e. Lat /\ X e. B /\ Y e. B ) -> ( X ./\ Y ) e. B )

  proof
    cK
    clat
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
    cK
    cjn
    cfv
    #
    co
    cB
    wcel
    cX
    cY
    c.an
    co
    cB
    wcel
    cB
    @0
    cK
    c.an
    cX
    cY
    latmcl.b
    @0
    eqid
    latmcl.m
    latlem
    simprd
end

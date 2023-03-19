include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cmee.mm"
include "cfv.mm"
include "eqid.mm"
include "latlem.mm"
include "simpld.mm"

theorem latjcl
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let cX: class X
  let cY: class Y
  assume latjcl.b: |- B = ( Base ` K )
  assume latjcl.j: |- .\/ = ( join ` K )


  assert |- ( ( K e. Lat /\ X e. B /\ Y e. B ) -> ( X .\/ Y ) e. B )

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
    c.or
    co
    cB
    wcel
    cX
    cY
    cK
    cmee
    cfv
    #
    co
    cB
    wcel
    cB
    c.or
    cK
    @0
    cX
    cY
    latjcl.b
    latjcl.j
    @0
    eqid
    latlem
    simpld
end

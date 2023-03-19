include "ccla.mm"
include "wcel.mm"
include "cglb.mm"
include "cfv.mm"
include "eqid.mm"
include "p0val.mm"
include "wss.mm"
include "ssid.mm"
include "clatglbcl.mm"
include "mpan2.mm"
include "eqeltrd.mm"

theorem clatp0cl
  let cB: class B
  let cW: class W
  let c.0: class .0.
  assume clatp0cl.b: |- B = ( Base ` W )
  assume clatp0cl.0: |- .0. = ( 0. ` W )


  assert |- ( W e. CLat -> .0. e. B )

  proof
    cW
    ccla
    wcel
    #
    c.0
    cB
    cW
    cglb
    cfv
    #
    cfv
    #
    cB
    cB
    @1
    cW
    ccla
    c.0
    clatp0cl.b
    @1
    eqid
    #
    clatp0cl.0
    p0val
    @0
    cB
    cB
    wss
    @2
    cB
    wcel
    cB
    ssid
    cB
    cB
    @1
    cW
    clatp0cl.b
    @3
    clatglbcl
    mpan2
    eqeltrd
end

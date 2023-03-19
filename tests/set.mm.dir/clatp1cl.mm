include "ccla.mm"
include "wcel.mm"
include "club.mm"
include "cfv.mm"
include "eqid.mm"
include "p1val.mm"
include "wss.mm"
include "ssid.mm"
include "clatlubcl.mm"
include "mpan2.mm"
include "eqeltrd.mm"

theorem clatp1cl
  let cB: class B
  let c.1: class .1.
  let cW: class W
  assume clatp1cl.b: |- B = ( Base ` W )
  assume clatp1cl.1: |- .1. = ( 1. ` W )


  assert |- ( W e. CLat -> .1. e. B )

  proof
    cW
    ccla
    wcel
    #
    c.1
    cB
    cW
    club
    cfv
    #
    cfv
    #
    cB
    cB
    @1
    c.1
    cW
    ccla
    clatp1cl.b
    @1
    eqid
    #
    clatp1cl.1
    p1val
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
    clatp1cl.b
    @3
    clatlubcl
    mpan2
    eqeltrd
end

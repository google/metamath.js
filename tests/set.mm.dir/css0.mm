include "cphl.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cocv.mm"
include "csn.mm"
include "eqid.mm"
include "ocv1.mm"
include "wss.mm"
include "ssid.mm"
include "ocvcss.mm"
include "mpan2.mm"
include "eqeltrrd.mm"

theorem css0
  let cC: class C
  let cW: class W
  let c.0: class .0.
  assume css0.c: |- C = ( CSubSp ` W )
  assume css0.z: |- .0. = ( 0g ` W )


  assert |- ( W e. PreHil -> { .0. } e. C )

  proof
    cW
    cphl
    wcel
    #
    cW
    cbs
    cfv
    #
    cW
    cocv
    cfv
    #
    cfv
    #
    c.0
    csn
    cC
    @2
    @1
    cW
    c.0
    @1
    eqid
    #
    @2
    eqid
    #
    css0.z
    ocv1
    @0
    @1
    @1
    wss
    @3
    cC
    wcel
    @1
    ssid
    cC
    @1
    @2
    @1
    cW
    @4
    css0.c
    @5
    ocvcss
    mpan2
    eqeltrrd
end

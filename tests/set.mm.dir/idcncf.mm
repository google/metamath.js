include "cc.mm"
include "cv.mm"
include "cmpt.mm"
include "ccncf.mm"
include "co.mm"
include "wss.mm"
include "wcel.mm"
include "ssid.mm"
include "cncfmptid.mm"
include "mp2an.mm"
include "eqeltri.mm"

theorem idcncf
  let vx: setvar x
  let cF: class F
  assume idcncf.1: |- F = ( x e. CC |-> x )


  assert |- F e. ( CC -cn-> CC )

  proof
    cF
    vx
    cc
    vx
    cv
    cmpt
    #
    cc
    cc
    ccncf
    co
    #
    idcncf.1
    cc
    cc
    wss
    #
    @2
    @0
    @1
    wcel
    cc
    ssid
    #
    @3
    vx
    cc
    cc
    cncfmptid
    mp2an
    eqeltri
end

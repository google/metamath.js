include "cv.mm"
include "cvv.mm"
include "wcel.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "csn.mm"
include "cop.mm"
include "cplusg.mm"
include "cmulr.mm"
include "ctp.mm"
include "crg.mm"
include "c0.mm"
include "wne.mm"
include "vex.mm"
include "eqid.mm"
include "ring1.mm"
include "ne0i.mm"
include "mp2b.mm"

theorem ringn0
  let vz: setvar z


  assert |- Ring =/= (/)

  proof
    vz
    cv
    #
    cvv
    wcel
    cnx
    cbs
    cfv
    @0
    csn
    cop
    cnx
    cplusg
    cfv
    @0
    @0
    cop
    @0
    cop
    csn
    #
    cop
    cnx
    cmulr
    cfv
    @1
    cop
    ctp
    #
    crg
    wcel
    crg
    c0
    wne
    vz
    vex
    @2
    cvv
    @0
    @2
    eqid
    ring1
    crg
    @2
    ne0i
    mp2b
end

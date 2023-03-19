include "cv.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "csn.mm"
include "cop.mm"
include "cplusg.mm"
include "csca.mm"
include "cmulr.mm"
include "ctp.mm"
include "cvsca.mm"
include "cun.mm"
include "clmod.mm"
include "c0.mm"
include "wne.mm"
include "vex.mm"
include "pm3.2i.mm"
include "eqid.mm"
include "lmod1zr.mm"
include "ne0i.mm"
include "mp2b.mm"

theorem lmodn0
  let vk: setvar k
  let vx: setvar x
  let vi: setvar i
  let vz: setvar z


  assert |- LMod =/= (/)

  proof
    vi
    cv
    #
    cvv
    wcel
    #
    vz
    cv
    #
    cvv
    wcel
    #
    wa
    cnx
    cbs
    cfv
    #
    @0
    csn
    cop
    cnx
    cplusg
    cfv
    #
    @0
    @0
    cop
    @0
    cop
    csn
    cop
    cnx
    csca
    cfv
    @4
    @2
    csn
    cop
    @5
    @2
    @2
    cop
    @2
    cop
    csn
    #
    cop
    cnx
    cmulr
    cfv
    @6
    cop
    ctp
    #
    cop
    ctp
    cnx
    cvsca
    cfv
    @2
    @0
    cop
    @0
    cop
    csn
    cop
    csn
    cun
    #
    clmod
    wcel
    clmod
    c0
    wne
    @1
    @3
    vi
    vex
    vz
    vex
    pm3.2i
    @7
    @0
    @8
    cvv
    cvv
    @2
    @7
    eqid
    @8
    eqid
    lmod1zr
    clmod
    @8
    ne0i
    mp2b
end

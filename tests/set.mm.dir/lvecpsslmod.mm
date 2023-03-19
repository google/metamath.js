include "clvec.mm"
include "clmod.mm"
include "wpss.mm"
include "wss.mm"
include "wne.mm"
include "cv.mm"
include "lveclmod.mm"
include "ssriv.mm"
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
include "wn.mm"
include "vex.mm"
include "pm3.2i.mm"
include "eqid.mm"
include "lmod1zr.mm"
include "wnel.mm"
include "lmod1zrnlvec.mm"
include "df-nel.mm"
include "sylib.mm"
include "jca.mm"
include "nelne1.mm"
include "necomd.mm"
include "mp2b.mm"
include "df-pss.mm"
include "mpbir2an.mm"

theorem lvecpsslmod
  let vk: setvar k
  let vx: setvar x
  let vv: setvar v
  let vi: setvar i
  let vz: setvar z


  assert |- LVec C. LMod

  proof
    clvec
    clmod
    wpss
    clvec
    clmod
    wss
    clvec
    clmod
    wne
    #
    vv
    clvec
    clmod
    vv
    cv
    lveclmod
    ssriv
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
    #
    cnx
    cbs
    cfv
    #
    @1
    csn
    cop
    cnx
    cplusg
    cfv
    #
    @1
    @1
    cop
    @1
    cop
    csn
    cop
    cnx
    csca
    cfv
    @6
    @3
    csn
    cop
    @7
    @3
    @3
    cop
    @3
    cop
    csn
    #
    cop
    cnx
    cmulr
    cfv
    @8
    cop
    ctp
    #
    cop
    ctp
    cnx
    cvsca
    cfv
    @3
    @1
    cop
    @1
    cop
    csn
    cop
    csn
    cun
    #
    clmod
    wcel
    #
    @10
    clvec
    wcel
    wn
    #
    wa
    #
    @0
    @2
    @4
    vi
    vex
    vz
    vex
    pm3.2i
    @5
    @11
    @12
    @9
    @1
    @10
    cvv
    cvv
    @3
    @9
    eqid
    #
    @10
    eqid
    #
    lmod1zr
    @5
    @10
    clvec
    wnel
    @12
    @9
    @1
    @10
    cvv
    cvv
    @3
    @14
    @15
    lmod1zrnlvec
    @10
    clvec
    df-nel
    sylib
    jca
    @13
    clmod
    clvec
    @10
    clmod
    clvec
    nelne1
    necomd
    mp2b
    clvec
    clmod
    df-pss
    mpbir2an
end

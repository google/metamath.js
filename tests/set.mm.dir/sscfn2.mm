include "cv.mm"
include "cxp.mm"
include "wfn.mm"
include "cfv.mm"
include "cpw.mm"
include "cixp.mm"
include "wcel.mm"
include "wrex.mm"
include "wa.mm"
include "wex.mm"
include "cssc.mm"
include "wbr.mm"
include "brssc.mm"
include "sylib.mm"
include "simpr.mm"
include "cdm.mm"
include "wceq.mm"
include "adantr.mm"
include "fndm.mm"
include "adantl.mm"
include "dmeqd.mm"
include "dmxpid.mm"
include "syl6eq.mm"
include "eqtr2d.mm"
include "sqxpeqd.mm"
include "fneq2d.mm"
include "mpbid.mm"
include "ex.mm"
include "adantrd.mm"
include "exlimdv.mm"
include "mpd.mm"

theorem sscfn2
  let wph: wff ph
  let cT: class T
  let cH: class H
  let cJ: class J
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  assume sscfn1.1: |- ( ph -> H C_cat J )
  assume sscfn2.2: |- ( ph -> T = dom dom J )


  assert |- ( ph -> J Fn ( T X. T ) )

  proof
    wph
    cJ
    vt
    cv
    #
    @0
    cxp
    #
    wfn
    #
    cH
    vx
    vy
    cv
    #
    @3
    cxp
    vx
    cv
    cJ
    cfv
    cpw
    cixp
    wcel
    vy
    @0
    cpw
    wrex
    #
    wa
    #
    vt
    wex
    #
    cJ
    cT
    cT
    cxp
    #
    wfn
    #
    wph
    cH
    cJ
    cssc
    wbr
    @6
    sscfn1.1
    vx
    vt
    cH
    cJ
    vy
    brssc
    sylib
    wph
    @5
    @8
    vt
    wph
    @2
    @8
    @4
    wph
    @2
    @8
    wph
    @2
    wa
    #
    @2
    @8
    wph
    @2
    simpr
    @9
    @1
    @7
    cJ
    @9
    @0
    cT
    @9
    cT
    cJ
    cdm
    #
    cdm
    #
    @0
    wph
    cT
    @11
    wceq
    @2
    sscfn2.2
    adantr
    @9
    @11
    @1
    cdm
    @0
    @9
    @10
    @1
    @2
    @10
    @1
    wceq
    wph
    @1
    cJ
    fndm
    adantl
    dmeqd
    @0
    dmxpid
    syl6eq
    eqtr2d
    sqxpeqd
    fneq2d
    mpbid
    ex
    adantrd
    exlimdv
    mpd
end

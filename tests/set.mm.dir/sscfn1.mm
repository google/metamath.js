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
include "ixpfn.mm"
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
include "syl5.mm"
include "rexlimdvw.mm"
include "adantld.mm"
include "exlimdv.mm"
include "mpd.mm"

theorem sscfn1
  let wph: wff ph
  let cS: class S
  let cH: class H
  let cJ: class J
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let cT: class T
  assume sscfn1.1: |- ( ph -> H C_cat J )
  assume sscfn1.2: |- ( ph -> S = dom dom H )


  assert |- ( ph -> H Fn ( S X. S ) )

  proof
    wph
    cJ
    vt
    cv
    #
    @0
    cxp
    wfn
    #
    cH
    vx
    vs
    cv
    #
    @2
    cxp
    #
    vx
    cv
    cJ
    cfv
    cpw
    #
    cixp
    wcel
    #
    vs
    @0
    cpw
    #
    wrex
    #
    wa
    #
    vt
    wex
    #
    cH
    cS
    cS
    cxp
    #
    wfn
    #
    wph
    cH
    cJ
    cssc
    wbr
    @9
    sscfn1.1
    vx
    vt
    cH
    cJ
    vs
    brssc
    sylib
    wph
    @8
    @11
    vt
    wph
    @7
    @11
    @1
    wph
    @5
    @11
    vs
    @6
    @5
    cH
    @3
    wfn
    #
    wph
    @11
    vx
    @3
    @4
    cH
    ixpfn
    wph
    @12
    @11
    wph
    @12
    wa
    #
    @12
    @11
    wph
    @12
    simpr
    @13
    @3
    @10
    cH
    @13
    @2
    cS
    @13
    cS
    cH
    cdm
    #
    cdm
    #
    @2
    wph
    cS
    @15
    wceq
    @12
    sscfn1.2
    adantr
    @13
    @15
    @3
    cdm
    @2
    @13
    @14
    @3
    @12
    @14
    @3
    wceq
    wph
    @3
    cH
    fndm
    adantl
    dmeqd
    @2
    dmxpid
    syl6eq
    eqtr2d
    sqxpeqd
    fneq2d
    mpbid
    ex
    syl5
    rexlimdvw
    adantld
    exlimdv
    mpd
end

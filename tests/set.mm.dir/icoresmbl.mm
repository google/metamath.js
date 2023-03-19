include "cico.mm"
include "cr.mm"
include "cxp.mm"
include "cres.mm"
include "crn.mm"
include "cvol.mm"
include "cdm.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "elicores.mm"
include "biimpi.mm"
include "wi.mm"
include "wa.mm"
include "simpr.mm"
include "cxr.mm"
include "simpl.mm"
include "rexr.mm"
include "adantl.mm"
include "icombl.mm"
include "syl2anc.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "ex.mm"
include "rexlimdva.mm"
include "rexlimiv.mm"
include "a1i.mm"
include "mpd.mm"
include "rgen.mm"
include "dfss3.mm"
include "mpbir.mm"

theorem icoresmbl
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k


  assert |- ran ( [,) |` ( RR X. RR ) ) C_ dom vol

  proof
    cico
    cr
    cr
    cxp
    cres
    crn
    #
    cvol
    cdm
    #
    wss
    vx
    cv
    #
    @1
    wcel
    #
    vx
    @0
    wral
    @3
    vx
    @0
    @2
    @0
    wcel
    #
    @2
    vy
    cv
    #
    vz
    cv
    #
    cico
    co
    #
    wceq
    #
    vz
    cr
    wrex
    #
    vy
    cr
    wrex
    #
    @3
    @4
    @10
    vy
    vz
    @2
    elicores
    biimpi
    @10
    @3
    wi
    @4
    @9
    @3
    vy
    cr
    @5
    cr
    wcel
    #
    @8
    @3
    vz
    cr
    @11
    @6
    cr
    wcel
    #
    wa
    #
    @8
    @3
    @13
    @8
    wa
    @2
    @7
    @1
    @13
    @8
    simpr
    @13
    @7
    @1
    wcel
    #
    @8
    @13
    @11
    @6
    cxr
    wcel
    #
    @14
    @11
    @12
    simpl
    @12
    @15
    @11
    @6
    rexr
    adantl
    @5
    @6
    icombl
    syl2anc
    adantr
    eqeltrd
    ex
    rexlimdva
    rexlimiv
    a1i
    mpd
    rgen
    vx
    @0
    @1
    dfss3
    mpbir
end

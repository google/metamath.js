include "ctop.mm"
include "wcel.mm"
include "wa.mm"
include "ccn.mm"
include "co.mm"
include "cuni.mm"
include "wss.mm"
include "cxko.mm"
include "cv.mm"
include "c0.mm"
include "cima.mm"
include "crab.mm"
include "wral.mm"
include "wceq.mm"
include "ima0.mm"
include "0ss.mm"
include "eqsstri.mm"
include "a1i.mm"
include "ralrimiva.mm"
include "rabid2.mm"
include "sylibr.mm"
include "eqid.mm"
include "simpl.mm"
include "simpr.mm"
include "crest.mm"
include "csn.mm"
include "ccmp.mm"
include "rest0.mm"
include "adantr.mm"
include "0cmp.mm"
include "syl6eqel.mm"
include "topopn.mm"
include "adantl.mm"
include "xkoopn.mm"
include "eqeltrd.mm"
include "syl6eleqr.mm"
include "elssuni.mm"
include "syl.mm"
include "cpw.mm"
include "cmpt2.mm"
include "crn.mm"
include "cfi.mm"
include "cfv.mm"
include "ctg.mm"
include "xkoval.mm"
include "unieqd.mm"
include "unieqi.mm"
include "cvv.mm"
include "ovex.mm"
include "pwex.mm"
include "cxp.mm"
include "wf.mm"
include "xkotf.mm"
include "frn.mm"
include "ax-mp.mm"
include "ssexi.mm"
include "fiuni.mm"
include "fvex.mm"
include "unitg.mm"
include "eqtr4i.mm"
include "3eqtr4g.mm"
include "sspwuni.mm"
include "sylib.mm"
include "eqsstrd.mm"
include "eqssd.mm"

theorem xkouni
  let cR: class R
  let cS: class S
  let cJ: class J
  let vf: setvar f
  let vk: setvar k
  let vv: setvar v
  let vx: setvar x
  assume xkouni.1: |- J = ( S ^ko R )


  assert |- ( ( R e. Top /\ S e. Top ) -> ( R Cn S ) = U. J )

  proof
    cR
    ctop
    wcel
    #
    cS
    ctop
    wcel
    #
    wa
    #
    cR
    cS
    ccn
    co
    #
    cJ
    cuni
    #
    @2
    @3
    cJ
    wcel
    @3
    @4
    wss
    @2
    @3
    cS
    cR
    cxko
    co
    #
    cJ
    @2
    @3
    vf
    cv
    #
    c0
    cima
    #
    cS
    cuni
    #
    wss
    #
    vf
    @3
    crab
    #
    @5
    @2
    @9
    vf
    @3
    wral
    @3
    @10
    wceq
    @2
    @9
    vf
    @3
    @9
    @2
    @6
    @3
    wcel
    wa
    @7
    c0
    @8
    @6
    ima0
    @8
    0ss
    eqsstri
    a1i
    ralrimiva
    @9
    vf
    @3
    rabid2
    sylibr
    @2
    c0
    cR
    cS
    @8
    vf
    cR
    cuni
    #
    @11
    eqid
    #
    @0
    @1
    simpl
    @0
    @1
    simpr
    c0
    @11
    wss
    @2
    @11
    0ss
    a1i
    @2
    cR
    c0
    crest
    co
    #
    c0
    csn
    #
    ccmp
    @0
    @13
    @14
    wceq
    @1
    cR
    rest0
    adantr
    0cmp
    syl6eqel
    @1
    @8
    cS
    wcel
    @0
    cS
    @8
    @8
    eqid
    topopn
    adantl
    xkoopn
    eqeltrd
    xkouni.1
    syl6eleqr
    @3
    cJ
    elssuni
    syl
    @2
    @4
    vk
    vv
    cR
    vx
    cv
    crest
    co
    ccmp
    wcel
    vx
    @11
    cpw
    crab
    #
    cS
    @6
    vk
    cv
    cima
    vv
    cv
    wss
    vf
    @3
    crab
    cmpt2
    #
    crn
    #
    cuni
    #
    @3
    @2
    @5
    cuni
    @17
    cfi
    cfv
    #
    ctg
    cfv
    #
    cuni
    #
    @4
    @18
    @2
    @5
    @20
    vx
    vv
    cR
    cS
    @16
    vf
    vk
    @15
    @11
    @12
    @15
    eqid
    #
    @16
    eqid
    #
    xkoval
    unieqd
    cJ
    @5
    xkouni.1
    unieqi
    @18
    @19
    cuni
    #
    @21
    @17
    cvv
    wcel
    @18
    @24
    wceq
    @17
    @3
    cpw
    #
    @3
    cR
    cS
    ccn
    ovex
    pwex
    @15
    cS
    cxp
    #
    @25
    @16
    wf
    @17
    @25
    wss
    #
    vx
    vv
    cR
    cS
    @16
    vf
    vk
    @15
    @11
    @12
    @22
    @23
    xkotf
    @26
    @25
    @16
    frn
    ax-mp
    #
    ssexi
    @17
    cvv
    fiuni
    ax-mp
    @19
    cvv
    wcel
    @21
    @24
    wceq
    @17
    cfi
    fvex
    @19
    cvv
    unitg
    ax-mp
    eqtr4i
    3eqtr4g
    @2
    @27
    @18
    @3
    wss
    @27
    @2
    @28
    a1i
    @17
    @3
    sspwuni
    sylib
    eqsstrd
    eqssd
end

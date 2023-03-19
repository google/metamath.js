include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cxp.mm"
include "cmul.mm"
include "cres.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "wa.mm"
include "ax-mulf.mm"
include "ffnov.mm"
include "mpbi.mm"
include "simpli.mm"
include "difss.mm"
include "xpss12.mm"
include "mp2an.mm"
include "fnssres.mm"
include "ovres.mm"
include "wne.mm"
include "eldifsn.mm"
include "mulcl.mm"
include "ad2ant2r.mm"
include "mulne0.mm"
include "jca.mm"
include "syl2anb.mm"
include "sylibr.mm"
include "eqeltrd.mm"
include "rgen2a.mm"
include "mpbir2an.mm"

theorem mulnzcnopr
  let vx: setvar x
  let vy: setvar y


  assert |- ( x. |` ( ( CC \ { 0 } ) X. ( CC \ { 0 } ) ) ) : ( ( CC \ { 0 } ) X. ( CC \ { 0 } ) ) --> ( CC \ { 0 } )

  proof
    cc
    cc0
    csn
    #
    cdif
    #
    @1
    cxp
    #
    @1
    cmul
    @2
    cres
    #
    wf
    @3
    @2
    wfn
    #
    vx
    cv
    #
    vy
    cv
    #
    @3
    co
    #
    @1
    wcel
    #
    vy
    @1
    wral
    vx
    @1
    wral
    cmul
    cc
    cc
    cxp
    #
    wfn
    #
    @2
    @9
    wss
    #
    @4
    @10
    @5
    @6
    cmul
    co
    #
    cc
    wcel
    #
    vy
    cc
    wral
    vx
    cc
    wral
    #
    @9
    cc
    cmul
    wf
    @10
    @14
    wa
    ax-mulf
    vx
    vy
    cc
    cc
    cc
    cmul
    ffnov
    mpbi
    simpli
    @1
    cc
    wss
    #
    @15
    @11
    cc
    @0
    difss
    #
    @16
    @1
    cc
    @1
    cc
    xpss12
    mp2an
    @9
    @2
    cmul
    fnssres
    mp2an
    @8
    vx
    vy
    @1
    @5
    @1
    wcel
    #
    @6
    @1
    wcel
    #
    wa
    #
    @7
    @12
    @1
    @5
    @6
    @1
    @1
    cmul
    ovres
    @19
    @13
    @12
    cc0
    wne
    #
    wa
    #
    @12
    @1
    wcel
    @17
    @5
    cc
    wcel
    #
    @5
    cc0
    wne
    #
    wa
    #
    @6
    cc
    wcel
    #
    @6
    cc0
    wne
    #
    wa
    #
    @21
    @18
    @5
    cc
    cc0
    eldifsn
    @6
    cc
    cc0
    eldifsn
    @24
    @27
    wa
    @13
    @20
    @22
    @25
    @13
    @23
    @26
    @5
    @6
    mulcl
    ad2ant2r
    @5
    @6
    mulne0
    jca
    syl2anb
    @12
    cc
    cc0
    eldifsn
    sylibr
    eqeltrd
    rgen2a
    vx
    vy
    @1
    @1
    @1
    @3
    ffnov
    mpbir2an
end

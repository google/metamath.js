include "wcel.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "wa.mm"
include "cdm.mm"
include "cuni.mm"
include "cpw.mm"
include "cv.mm"
include "wss.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "crab.mm"
include "cfv.mm"
include "cesum.mm"
include "cmpt.mm"
include "crn.mm"
include "clt.mm"
include "cinf.mm"
include "coms.mm"
include "wor.mm"
include "cxr.mm"
include "iccssxr.mm"
include "xrltso.mm"
include "soss.mm"
include "mp2.mm"
include "a1i.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "omscl.mm"
include "3expa.mm"
include "xrge0infss.mm"
include "syl.mm"
include "infcl.mm"
include "cvv.mm"
include "wceq.mm"
include "fex.mm"
include "ancoms.mm"
include "omsval.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "fdm.mm"
include "unieqd.mm"
include "pweqd.mm"
include "ad2antlr.mm"
include "eleqtrd.mm"
include "elpwi.mm"
include "omsfval.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "fmpt2d.mm"

theorem omsf
  let cQ: class Q
  let cR: class R
  let cV: class V
  let va: setvar a
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A


  assert |- ( ( Q e. V /\ R : Q --> ( 0 [,] +oo ) ) -> ( toOMeas ` R ) : ~P U. dom R --> ( 0 [,] +oo ) )

  proof
    cQ
    cV
    wcel
    #
    cQ
    cc0
    cpnf
    cicc
    co
    #
    cR
    wf
    #
    wa
    #
    va
    va
    cR
    cdm
    #
    cuni
    #
    cpw
    #
    vx
    va
    cv
    #
    vz
    cv
    #
    cuni
    wss
    @8
    com
    cdom
    wbr
    wa
    vz
    @4
    cpw
    crab
    vx
    cv
    vy
    cv
    cR
    cfv
    vy
    cesum
    cmpt
    crn
    #
    @1
    clt
    cinf
    #
    @1
    cR
    coms
    cfv
    #
    @1
    @3
    @7
    @6
    wcel
    #
    wa
    #
    vt
    vw
    vs
    @1
    @9
    clt
    @1
    clt
    wor
    #
    @13
    @1
    cxr
    wss
    cxr
    clt
    wor
    @14
    cc0
    cpnf
    iccssxr
    xrltso
    @1
    cxr
    clt
    soss
    mp2
    a1i
    @13
    @9
    @1
    wss
    #
    vw
    cv
    #
    vt
    cv
    #
    clt
    wbr
    wn
    vw
    @9
    wral
    @17
    @16
    clt
    wbr
    vs
    cv
    @16
    clt
    wbr
    vs
    @9
    wrex
    wi
    vw
    @1
    wral
    wa
    vt
    @1
    wrex
    @0
    @2
    @12
    @15
    vx
    vy
    vz
    @7
    cQ
    cR
    cV
    omscl
    3expa
    vt
    vw
    vs
    @9
    xrge0infss
    syl
    infcl
    #
    @3
    cR
    cvv
    wcel
    #
    @11
    va
    @6
    @10
    cmpt
    wceq
    @2
    @0
    @19
    cQ
    @1
    cV
    cR
    fex
    ancoms
    vx
    vy
    vz
    cR
    va
    omsval
    syl
    @13
    @7
    @11
    cfv
    #
    @10
    @1
    @13
    @0
    @2
    @7
    cQ
    cuni
    #
    wss
    #
    @20
    @10
    wceq
    @0
    @2
    @12
    simpll
    @0
    @2
    @12
    simplr
    @13
    @7
    @21
    cpw
    #
    wcel
    @22
    @13
    @7
    @6
    @23
    @3
    @12
    simpr
    @2
    @6
    @23
    wceq
    @0
    @12
    @2
    @5
    @21
    @2
    @4
    cQ
    cQ
    @1
    cR
    fdm
    unieqd
    pweqd
    ad2antlr
    eleqtrd
    @7
    @21
    elpwi
    syl
    vx
    vy
    vz
    @7
    cQ
    cR
    cV
    omsfval
    syl3anc
    @18
    eqeltrd
    fmpt2d
end

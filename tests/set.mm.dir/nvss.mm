include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "cvc.mm"
include "wcel.mm"
include "crn.mm"
include "cr.mm"
include "wf.mm"
include "cfv.mm"
include "cc0.mm"
include "cgi.mm"
include "wi.mm"
include "co.mm"
include "cabs.mm"
include "cmul.mm"
include "cc.mm"
include "wral.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "wa.mm"
include "wex.mm"
include "copab.mm"
include "cvv.mm"
include "cnv.mm"
include "cxp.mm"
include "eleq1.mm"
include "biimpar.mm"
include "3ad2antr1.mm"
include "exlimivv.mm"
include "vex.mm"
include "jctir.mm"
include "ssopab2i.mm"
include "coprab.mm"
include "df-nv.mm"
include "dfoprab2.mm"
include "eqtri.mm"
include "df-xp.mm"
include "3sstr4i.mm"

theorem nvss
  let vg: setvar g
  let vs: setvar s
  let vn: setvar n
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let cN: class N


  assert |- NrmCVec C_ ( CVecOLD X. _V )

  proof
    vw
    cv
    #
    vg
    cv
    #
    vs
    cv
    #
    cop
    #
    wceq
    #
    @3
    cvc
    wcel
    #
    @1
    crn
    #
    cr
    vn
    cv
    #
    wf
    #
    vx
    cv
    #
    @7
    cfv
    #
    cc0
    wceq
    @9
    @1
    cgi
    cfv
    wceq
    wi
    vy
    cv
    #
    @9
    @2
    co
    @7
    cfv
    @11
    cabs
    cfv
    @10
    cmul
    co
    wceq
    vy
    cc
    wral
    @9
    @11
    @1
    co
    @7
    cfv
    @10
    @11
    @7
    cfv
    caddc
    co
    cle
    wbr
    vy
    @6
    wral
    w3a
    vx
    @6
    wral
    #
    w3a
    #
    wa
    #
    vs
    wex
    vg
    wex
    #
    vw
    vn
    copab
    #
    @0
    cvc
    wcel
    #
    @7
    cvv
    wcel
    #
    wa
    #
    vw
    vn
    copab
    cnv
    cvc
    cvv
    cxp
    @15
    @19
    vw
    vn
    @15
    @17
    @18
    @14
    @17
    vg
    vs
    @4
    @8
    @5
    @17
    @12
    @4
    @17
    @5
    @0
    @3
    cvc
    eleq1
    biimpar
    3ad2antr1
    exlimivv
    vn
    vex
    jctir
    ssopab2i
    cnv
    @13
    vg
    vs
    vn
    coprab
    @16
    vx
    vy
    vg
    vn
    vs
    df-nv
    @13
    vg
    vs
    vn
    vw
    dfoprab2
    eqtri
    vw
    vn
    cvc
    cvv
    df-xp
    3sstr4i
end

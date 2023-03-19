include "csslt.mm"
include "csur.mm"
include "cscut.mm"
include "wf.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "cpw.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cbday.mm"
include "cfv.mm"
include "wbr.mm"
include "wa.mm"
include "crab.mm"
include "cint.mm"
include "crio.mm"
include "df-scut.mm"
include "mpt2fun.mm"
include "dmscut.mm"
include "df-fn.mm"
include "mpbir2an.mm"
include "wrex.mm"
include "cab.mm"
include "rnmpt2.mm"
include "wcel.mm"
include "wi.mm"
include "cop.mm"
include "vex.mm"
include "elimasn.mm"
include "df-br.mm"
include "bitr4i.mm"
include "co.mm"
include "scutval.mm"
include "scutcut.mm"
include "simp1d.mm"
include "eqeltrrd.mm"
include "sylbi.mm"
include "eleq1a.mm"
include "syl.mm"
include "adantl.mm"
include "rexlimivv.mm"
include "abssi.mm"
include "eqsstri.mm"
include "df-f.mm"

theorem scutf
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- |s : <<s --> No

  proof
    csslt
    csur
    cscut
    wf
    cscut
    csslt
    wfn
    #
    cscut
    crn
    #
    csur
    wss
    @0
    cscut
    wfun
    cscut
    cdm
    csslt
    wceq
    va
    vb
    csur
    cpw
    #
    csslt
    va
    cv
    #
    csn
    cima
    #
    vx
    cv
    cbday
    cfv
    cbday
    @3
    vy
    cv
    csn
    #
    csslt
    wbr
    @5
    vb
    cv
    #
    csslt
    wbr
    wa
    vy
    csur
    crab
    #
    cima
    cint
    wceq
    vx
    @7
    crio
    #
    cscut
    vx
    vy
    va
    vb
    df-scut
    #
    mpt2fun
    dmscut
    cscut
    csslt
    df-fn
    mpbir2an
    @1
    vz
    cv
    #
    @8
    wceq
    #
    vb
    @4
    wrex
    va
    @2
    wrex
    #
    vz
    cab
    csur
    va
    vb
    vz
    @2
    @4
    @8
    cscut
    @9
    rnmpt2
    @12
    vz
    csur
    @11
    @10
    csur
    wcel
    #
    va
    vb
    @2
    @4
    @6
    @4
    wcel
    #
    @11
    @13
    wi
    #
    @3
    @2
    wcel
    @14
    @8
    csur
    wcel
    #
    @15
    @14
    @3
    @6
    csslt
    wbr
    #
    @16
    @14
    @3
    @6
    cop
    csslt
    wcel
    @17
    csslt
    @3
    @6
    va
    vex
    vb
    vex
    elimasn
    @3
    @6
    csslt
    df-br
    bitr4i
    @17
    @3
    @6
    cscut
    co
    #
    @8
    csur
    vx
    vy
    @3
    @6
    scutval
    @17
    @18
    csur
    wcel
    @3
    @18
    csn
    #
    csslt
    wbr
    @19
    @6
    csslt
    wbr
    @3
    @6
    scutcut
    simp1d
    eqeltrrd
    sylbi
    @8
    csur
    @10
    eleq1a
    syl
    adantl
    rexlimivv
    abssi
    eqsstri
    csslt
    csur
    cscut
    df-f
    mpbir2an
end

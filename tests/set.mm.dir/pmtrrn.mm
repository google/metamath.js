include "wcel.mm"
include "wss.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "w3a.mm"
include "cfv.mm"
include "crn.mm"
include "cv.mm"
include "cpw.mm"
include "crab.mm"
include "wfn.mm"
include "csn.mm"
include "cdif.mm"
include "cuni.mm"
include "cif.mm"
include "cmpt.mm"
include "cvv.mm"
include "wral.mm"
include "mptexg.mm"
include "ralrimivw.mm"
include "3ad2ant1.mm"
include "eqid.mm"
include "fnmpt.mm"
include "syl.mm"
include "wceq.mm"
include "pmtrfval.mm"
include "fneq1d.mm"
include "mpbird.mm"
include "elpw2g.mm"
include "biimpar.mm"
include "3adant3.mm"
include "simp3.mm"
include "breq1.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "fnfvelrn.mm"
include "syl2anc.mm"
include "syl6eleqr.mm"

theorem pmtrrn
  let cD: class D
  let cP: class P
  let cR: class R
  let cT: class T
  let cV: class V
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  assume pmtrrn.t: |- T = ( pmTrsp ` D )
  assume pmtrrn.r: |- R = ran T


  assert |- ( ( D e. V /\ P C_ D /\ P ~~ 2o ) -> ( T ` P ) e. R )

  proof
    cD
    cV
    wcel
    #
    cP
    cD
    wss
    #
    cP
    c2o
    cen
    wbr
    #
    w3a
    #
    cP
    cT
    cfv
    #
    cT
    crn
    #
    cR
    @3
    cT
    vx
    cv
    #
    c2o
    cen
    wbr
    #
    vx
    cD
    cpw
    #
    crab
    #
    wfn
    #
    cP
    @9
    wcel
    #
    @4
    @5
    wcel
    @3
    @10
    vz
    @9
    vy
    cD
    vy
    cv
    #
    vz
    cv
    #
    wcel
    @13
    @12
    csn
    cdif
    cuni
    @12
    cif
    #
    cmpt
    #
    cmpt
    #
    @9
    wfn
    #
    @3
    @15
    cvv
    wcel
    #
    vz
    @9
    wral
    #
    @17
    @0
    @1
    @19
    @2
    @0
    @18
    vz
    @9
    vy
    cD
    @14
    cV
    mptexg
    ralrimivw
    3ad2ant1
    vz
    @9
    @15
    @16
    cvv
    @16
    eqid
    fnmpt
    syl
    @3
    @9
    cT
    @16
    @0
    @1
    cT
    @16
    wceq
    @2
    vx
    vy
    cD
    cT
    cV
    vz
    pmtrrn.t
    pmtrfval
    3ad2ant1
    fneq1d
    mpbird
    @3
    cP
    @8
    wcel
    #
    @2
    @11
    @0
    @1
    @20
    @2
    @0
    @20
    @1
    cP
    cD
    cV
    elpw2g
    biimpar
    3adant3
    @0
    @1
    @2
    simp3
    @7
    @2
    vx
    cP
    @8
    @6
    cP
    c2o
    cen
    breq1
    elrab
    sylanbrc
    @9
    cP
    cT
    fnfvelrn
    syl2anc
    pmtrrn.r
    syl6eleqr
end

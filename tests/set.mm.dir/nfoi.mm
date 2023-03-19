include "coi.mm"
include "wwe.mm"
include "wse.mm"
include "wa.mm"
include "cvv.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "crn.mm"
include "wral.mm"
include "crab.mm"
include "crio.mm"
include "cmpt.mm"
include "crecs.mm"
include "cima.mm"
include "wrex.mm"
include "con0.mm"
include "cres.mm"
include "c0.mm"
include "cif.mm"
include "df-oi.mm"
include "nfwe.mm"
include "nfse.mm"
include "nfan.mm"
include "nfcv.mm"
include "nfbr.mm"
include "nfral.mm"
include "nfrab.mm"
include "nfn.mm"
include "nfriota.mm"
include "nfmpt.mm"
include "nfrecs.mm"
include "nfima.mm"
include "nfrex.mm"
include "nfres.mm"
include "nfif.mm"
include "nfcxfr.mm"

theorem nfoi
  let vx: setvar x
  let cA: class A
  let cR: class R
  let va: setvar a
  let vh: setvar h
  let vj: setvar j
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  assume nfoi.1: |- F/_ x R
  assume nfoi.2: |- F/_ x A


  assert |- F/_ x OrdIso ( R , A )

  proof
    vx
    cA
    cR
    coi
    cA
    cR
    wwe
    #
    cA
    cR
    wse
    #
    wa
    #
    vh
    cvv
    vu
    cv
    #
    vv
    cv
    #
    cR
    wbr
    #
    wn
    #
    vu
    vj
    cv
    #
    vw
    cv
    #
    cR
    wbr
    #
    vj
    vh
    cv
    crn
    #
    wral
    #
    vw
    cA
    crab
    #
    wral
    #
    vv
    @12
    crio
    #
    cmpt
    #
    crecs
    #
    vz
    cv
    #
    vt
    cv
    #
    cR
    wbr
    #
    vz
    @16
    va
    cv
    #
    cima
    #
    wral
    #
    vt
    cA
    wrex
    #
    va
    con0
    crab
    #
    cres
    #
    c0
    cif
    va
    vz
    vw
    vv
    vu
    vt
    cA
    cR
    vh
    vj
    df-oi
    @2
    vx
    @25
    c0
    @0
    @1
    vx
    vx
    cA
    cR
    nfoi.1
    nfoi.2
    nfwe
    vx
    cA
    cR
    nfoi.1
    nfoi.2
    nfse
    nfan
    vx
    @16
    @24
    vx
    @15
    vx
    vh
    cvv
    @14
    vx
    cvv
    nfcv
    @13
    vx
    vv
    @12
    @6
    vx
    vu
    @12
    @11
    vx
    vw
    cA
    @9
    vx
    vj
    @10
    vx
    @10
    nfcv
    vx
    @7
    @8
    cR
    vx
    @7
    nfcv
    nfoi.1
    vx
    @8
    nfcv
    nfbr
    nfral
    nfoi.2
    nfrab
    #
    @5
    vx
    vx
    @3
    @4
    cR
    vx
    @3
    nfcv
    nfoi.1
    vx
    @4
    nfcv
    nfbr
    nfn
    nfral
    @26
    nfriota
    nfmpt
    nfrecs
    #
    @23
    vx
    va
    con0
    @22
    vx
    vt
    cA
    nfoi.2
    @19
    vx
    vz
    @21
    vx
    @16
    @20
    @27
    vx
    @20
    nfcv
    nfima
    vx
    @17
    @18
    cR
    vx
    @17
    nfcv
    nfoi.1
    vx
    @18
    nfcv
    nfbr
    nfral
    nfrex
    vx
    con0
    nfcv
    nfrab
    nfres
    vx
    c0
    nfcv
    nfif
    nfcxfr
end

include "clvec.mm"
include "wcel.mm"
include "w3a.mm"
include "clss.mm"
include "cfv.mm"
include "cmri.mm"
include "cmrc.mm"
include "cbs.mm"
include "cacs.mm"
include "cv.mm"
include "csn.mm"
include "cun.mm"
include "cdif.mm"
include "wral.mm"
include "cpw.mm"
include "wa.mm"
include "eqid.mm"
include "lssacsex.mm"
include "3ad2ant1.mm"
include "simpld.mm"
include "simprd.mm"
include "wceq.mm"
include "simp2.mm"
include "wb.mm"
include "lbsacsbs.mm"
include "mpbid.mm"
include "simp3.mm"
include "eqtr4d.mm"
include "acsexdimd.mm"

theorem lvecdim
  let cS: class S
  let cT: class T
  let cJ: class J
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume lvecdim.1: |- J = ( LBasis ` W )


  assert |- ( ( W e. LVec /\ S e. J /\ T e. J ) -> S ~~ T )

  proof
    cW
    clvec
    wcel
    #
    cS
    cJ
    wcel
    #
    cT
    cJ
    wcel
    #
    w3a
    #
    vy
    vz
    cW
    clss
    cfv
    #
    cS
    cT
    @4
    cmri
    cfv
    #
    @4
    cmrc
    cfv
    #
    cW
    cbs
    cfv
    #
    vx
    @3
    @4
    @7
    cacs
    cfv
    wcel
    #
    vy
    cv
    #
    vx
    cv
    #
    vz
    cv
    csn
    cun
    @6
    cfv
    wcel
    vz
    @10
    @9
    csn
    cun
    @6
    cfv
    @10
    @6
    cfv
    cdif
    wral
    vy
    @7
    wral
    vx
    @7
    cpw
    wral
    #
    @0
    @1
    @8
    @11
    wa
    @2
    vy
    vz
    @4
    @6
    cW
    @7
    vx
    @4
    eqid
    #
    @6
    eqid
    #
    @7
    eqid
    #
    lssacsex
    3ad2ant1
    #
    simpld
    @13
    @5
    eqid
    #
    @3
    @8
    @11
    @15
    simprd
    @3
    cS
    @5
    wcel
    #
    cS
    @6
    cfv
    #
    @7
    wceq
    #
    @3
    @1
    @17
    @19
    wa
    #
    @0
    @1
    @2
    simp2
    @0
    @1
    @1
    @20
    wb
    @2
    @4
    cS
    @5
    cJ
    @6
    cW
    @7
    @12
    @13
    @14
    @16
    lvecdim.1
    lbsacsbs
    3ad2ant1
    mpbid
    #
    simpld
    @3
    cT
    @5
    wcel
    #
    cT
    @6
    cfv
    #
    @7
    wceq
    #
    @3
    @2
    @22
    @24
    wa
    #
    @0
    @1
    @2
    simp3
    @0
    @1
    @2
    @25
    wb
    @2
    @4
    cT
    @5
    cJ
    @6
    cW
    @7
    @12
    @13
    @14
    @16
    lvecdim.1
    lbsacsbs
    3ad2ant1
    mpbid
    #
    simpld
    @3
    @18
    @7
    @23
    @3
    @17
    @19
    @21
    simprd
    @3
    @22
    @24
    @26
    simprd
    eqtr4d
    acsexdimd
end

include "ccom.mm"
include "clo.mm"
include "wcel.mm"
include "chil.mm"
include "wf.mm"
include "cv.mm"
include "csm.mm"
include "co.mm"
include "cva.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "cc.mm"
include "lnopfi.mm"
include "hocofi.mm"
include "wa.mm"
include "w3a.mm"
include "lnopli.mm"
include "fveq2d.mm"
include "id.mm"
include "ffvelrni.mm"
include "syl3an.mm"
include "eqtrd.mm"
include "3expa.mm"
include "hvmulcl.mm"
include "hvaddcl.mm"
include "sylan.mm"
include "hocoi.mm"
include "syl.mm"
include "oveq2d.mm"
include "adantl.mm"
include "oveqan12d.mm"
include "3eqtr4d.mm"
include "3impa.mm"
include "rgen3.mm"
include "ellnop.mm"
include "mpbir2an.mm"

theorem lnopcoi
  let cS: class S
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume lnopco.1: |- S e. LinOp
  assume lnopco.2: |- T e. LinOp


  assert |- ( S o. T ) e. LinOp

  proof
    cS
    cT
    ccom
    #
    clo
    wcel
    chil
    chil
    @0
    wf
    vx
    cv
    #
    vy
    cv
    #
    csm
    co
    #
    vz
    cv
    #
    cva
    co
    #
    @0
    cfv
    #
    @1
    @2
    @0
    cfv
    #
    csm
    co
    #
    @4
    @0
    cfv
    #
    cva
    co
    #
    wceq
    #
    vz
    chil
    wral
    vy
    chil
    wral
    vx
    cc
    wral
    cS
    cT
    cS
    lnopco.1
    lnopfi
    #
    cT
    lnopco.2
    lnopfi
    #
    hocofi
    @11
    vx
    vy
    vz
    cc
    chil
    chil
    @1
    cc
    wcel
    #
    @2
    chil
    wcel
    #
    @4
    chil
    wcel
    #
    @11
    @14
    @15
    wa
    #
    @16
    wa
    #
    @5
    cT
    cfv
    #
    cS
    cfv
    #
    @1
    @2
    cT
    cfv
    #
    cS
    cfv
    #
    csm
    co
    #
    @4
    cT
    cfv
    #
    cS
    cfv
    #
    cva
    co
    #
    @6
    @10
    @14
    @15
    @16
    @20
    @26
    wceq
    @14
    @15
    @16
    w3a
    #
    @20
    @1
    @21
    csm
    co
    @24
    cva
    co
    #
    cS
    cfv
    #
    @26
    @27
    @19
    @28
    cS
    @1
    @2
    @4
    cT
    lnopco.2
    lnopli
    fveq2d
    @14
    @14
    @15
    @21
    chil
    wcel
    @16
    @24
    chil
    wcel
    @29
    @26
    wceq
    @14
    id
    chil
    chil
    @2
    cT
    @13
    ffvelrni
    chil
    chil
    @4
    cT
    @13
    ffvelrni
    @1
    @21
    @24
    cS
    lnopco.1
    lnopli
    syl3an
    eqtrd
    3expa
    @18
    @5
    chil
    wcel
    #
    @6
    @20
    wceq
    @17
    @3
    chil
    wcel
    @16
    @30
    @1
    @2
    hvmulcl
    @3
    @4
    hvaddcl
    sylan
    @5
    cS
    cT
    @12
    @13
    hocoi
    syl
    @17
    @16
    @8
    @23
    @9
    @25
    cva
    @15
    @8
    @23
    wceq
    @14
    @15
    @7
    @22
    @1
    csm
    @2
    cS
    cT
    @12
    @13
    hocoi
    oveq2d
    adantl
    @4
    cS
    cT
    @12
    @13
    hocoi
    oveqan12d
    3eqtr4d
    3impa
    rgen3
    vx
    vy
    vz
    @0
    ellnop
    mpbir2an
end

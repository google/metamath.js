include "cv.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cz.mm"
include "wrex.mm"
include "cn0.mm"
include "crab.mm"
include "wcel.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "wa.mm"
include "wb.mm"
include "nn0z.mm"
include "zsubcl.mm"
include "sylancr.mm"
include "divides.mm"
include "cc.mm"
include "nn0cn.mm"
include "zmulcl.mm"
include "mpan2.mm"
include "zcnd.mm"
include "zcn.mm"
include "ax-mp.mm"
include "subadd.mm"
include "mp3an1.mm"
include "addcom.mm"
include "eqeq1d.mm"
include "bitrd.mm"
include "syl2an.mm"
include "eqcom.mm"
include "3bitr3g.mm"
include "rexbidva.mm"
include "pm5.32i.mm"
include "oveq2.mm"
include "breq2d.mm"
include "elrab2.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "elrab.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem divalglem4
  let cD: class D
  let cS: class S
  let cN: class N
  let vr: setvar r
  let vq: setvar q
  let vx: setvar x
  let vz: setvar z
  let cR: class R
  assume divalglem0.1: |- N e. ZZ
  assume divalglem0.2: |- D e. ZZ
  assume divalglem1.3: |- D =/= 0
  assume divalglem2.4: |- S = { r e. NN0 | D || ( N - r ) }

  disjoint D r
  disjoint N r
  disjoint D q
  disjoint q r
  disjoint N q
  disjoint D x
  disjoint D z
  disjoint q x
  disjoint q z
  disjoint r x
  disjoint r z
  disjoint x z
  disjoint N x
  disjoint N z
  disjoint R x
  disjoint S z
  assert |- S = { r e. NN0 | E. q e. ZZ N = ( ( q x. D ) + r ) }

  proof
    vz
    cS
    cN
    vq
    cv
    #
    cD
    cmul
    co
    #
    vr
    cv
    #
    caddc
    co
    #
    wceq
    #
    vq
    cz
    wrex
    #
    vr
    cn0
    crab
    #
    vz
    cv
    #
    cn0
    wcel
    #
    cD
    cN
    @7
    cmin
    co
    #
    cdvds
    wbr
    #
    wa
    @8
    cN
    @1
    @7
    caddc
    co
    #
    wceq
    #
    vq
    cz
    wrex
    #
    wa
    @7
    cS
    wcel
    @7
    @6
    wcel
    @8
    @10
    @13
    @8
    @10
    @1
    @9
    wceq
    #
    vq
    cz
    wrex
    #
    @13
    @8
    cD
    cz
    wcel
    #
    @9
    cz
    wcel
    #
    @10
    @15
    wb
    divalglem0.2
    @8
    cN
    cz
    wcel
    #
    @7
    cz
    wcel
    @17
    divalglem0.1
    @7
    nn0z
    cN
    @7
    zsubcl
    sylancr
    vq
    cD
    @9
    divides
    sylancr
    @8
    @14
    @12
    vq
    cz
    @8
    @0
    cz
    wcel
    #
    wa
    @9
    @1
    wceq
    #
    @11
    cN
    wceq
    #
    @14
    @12
    @8
    @7
    cc
    wcel
    #
    @1
    cc
    wcel
    #
    @20
    @21
    wb
    @19
    @7
    nn0cn
    @19
    @1
    @19
    @16
    @1
    cz
    wcel
    divalglem0.2
    @0
    cD
    zmulcl
    mpan2
    zcnd
    @22
    @23
    wa
    #
    @20
    @7
    @1
    caddc
    co
    #
    cN
    wceq
    #
    @21
    cN
    cc
    wcel
    #
    @22
    @23
    @20
    @26
    wb
    @18
    @27
    divalglem0.1
    cN
    zcn
    ax-mp
    cN
    @7
    @1
    subadd
    mp3an1
    @24
    @25
    @11
    cN
    @7
    @1
    addcom
    eqeq1d
    bitrd
    syl2an
    @9
    @1
    eqcom
    @11
    cN
    eqcom
    3bitr3g
    rexbidva
    bitrd
    pm5.32i
    cD
    cN
    @2
    cmin
    co
    #
    cdvds
    wbr
    @10
    vr
    @7
    cn0
    cS
    @2
    @7
    wceq
    #
    @28
    @9
    cD
    cdvds
    @2
    @7
    cN
    cmin
    oveq2
    breq2d
    divalglem2.4
    elrab2
    @5
    @13
    vr
    @7
    cn0
    @29
    @4
    @12
    vq
    cz
    @29
    @3
    @11
    cN
    @2
    @7
    @1
    caddc
    oveq2
    eqeq2d
    rexbidv
    elrab
    3bitr4i
    eqriv
end

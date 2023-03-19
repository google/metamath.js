include "cgrp.mm"
include "wcel.mm"
include "cmnd.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "2zrngamnd.mm"
include "cneg.mm"
include "cz.mm"
include "c2.mm"
include "cmul.mm"
include "wa.mm"
include "weq.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elrab2.mm"
include "znegcl.mm"
include "adantr.mm"
include "nfv.mm"
include "nfre1.mm"
include "adantl.mm"
include "wb.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "negeq.mm"
include "2cnd.mm"
include "zcn.mm"
include "mulneg2d.mm"
include "eqcomd.mm"
include "sylan9eqr.mm"
include "rspcedvd.mm"
include "cbvrexv.mm"
include "sylibr.mm"
include "exp31.mm"
include "rexlimd.mm"
include "imp.mm"
include "sylanbrc.mm"
include "sylbi.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "crab.mm"
include "elrabi.mm"
include "eleq2s.mm"
include "zcnd.mm"
include "negcld.mm"
include "addcomd.mm"
include "negidd.mm"
include "eqtrd.mm"
include "rgen.mm"
include "2zrngbas.mm"
include "2zrngadd.mm"
include "2zrng0.mm"
include "isgrp.mm"
include "mpbir2an.mm"

theorem 2zrngagrp
  let vx: setvar x
  let vz: setvar z
  let cR: class R
  let cE: class E
  let va: setvar a
  let vb: setvar b
  let vy: setvar y
  let vk: setvar k
  assume 2zrng.e: |- E = { z e. ZZ | E. x e. ZZ z = ( 2 x. x ) }
  assume 2zrngbas.r: |- R = ( CCfld |`s E )

  disjoint x z
  disjoint R x
  disjoint R z
  disjoint E x
  disjoint E z
  disjoint E a
  disjoint E b
  disjoint a b
  disjoint R a
  disjoint R b
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint x y
  disjoint y z
  disjoint R y
  disjoint E y
  disjoint k x
  assert |- R e. Grp

  proof
    cR
    cgrp
    wcel
    cR
    cmnd
    wcel
    vz
    cv
    #
    vy
    cv
    #
    caddc
    co
    #
    cc0
    wceq
    #
    vz
    cE
    wrex
    #
    vy
    cE
    wral
    vx
    vz
    cR
    cE
    2zrng.e
    2zrngbas.r
    2zrngamnd
    @4
    vy
    cE
    @1
    cE
    wcel
    #
    @3
    @1
    cneg
    #
    @1
    caddc
    co
    #
    cc0
    wceq
    #
    vz
    @6
    cE
    @5
    @1
    cz
    wcel
    #
    @1
    c2
    vx
    cv
    #
    cmul
    co
    #
    wceq
    #
    vx
    cz
    wrex
    #
    wa
    #
    @6
    cE
    wcel
    #
    @0
    @11
    wceq
    #
    vx
    cz
    wrex
    #
    @13
    vz
    @1
    cz
    cE
    vz
    vy
    weq
    @16
    @12
    vx
    cz
    @0
    @1
    @11
    eqeq1
    rexbidv
    2zrng.e
    elrab2
    @14
    @6
    cz
    wcel
    #
    @6
    @11
    wceq
    #
    vx
    cz
    wrex
    #
    @15
    @9
    @18
    @13
    @1
    znegcl
    adantr
    @9
    @13
    @20
    @9
    @12
    @20
    vx
    cz
    @9
    vx
    nfv
    @19
    vx
    cz
    nfre1
    @9
    @10
    cz
    wcel
    #
    @12
    @20
    @9
    @21
    wa
    #
    @12
    wa
    #
    @6
    c2
    @0
    cmul
    co
    #
    wceq
    #
    vz
    cz
    wrex
    @20
    @23
    @25
    @6
    c2
    @10
    cneg
    #
    cmul
    co
    #
    wceq
    #
    vz
    @26
    cz
    @22
    @26
    cz
    wcel
    #
    @12
    @21
    @29
    @9
    @10
    znegcl
    adantl
    adantr
    @0
    @26
    wceq
    #
    @25
    @28
    wb
    @23
    @30
    @24
    @27
    @6
    @0
    @26
    c2
    cmul
    oveq2
    eqeq2d
    adantl
    @12
    @22
    @6
    @11
    cneg
    #
    @27
    @1
    @11
    negeq
    @21
    @31
    @27
    wceq
    @9
    @21
    @27
    @31
    @21
    c2
    @10
    @21
    2cnd
    @10
    zcn
    mulneg2d
    eqcomd
    adantl
    sylan9eqr
    rspcedvd
    @19
    @25
    vx
    vz
    cz
    vx
    vz
    weq
    @11
    @24
    @6
    @10
    @0
    c2
    cmul
    oveq2
    eqeq2d
    cbvrexv
    sylibr
    exp31
    rexlimd
    imp
    @17
    @20
    vz
    @6
    cz
    cE
    @0
    @6
    wceq
    #
    @16
    @19
    vx
    cz
    @0
    @6
    @11
    eqeq1
    rexbidv
    2zrng.e
    elrab2
    sylanbrc
    sylbi
    @32
    @3
    @8
    wb
    @5
    @32
    @2
    @7
    cc0
    @0
    @6
    @1
    caddc
    oveq1
    eqeq1d
    adantl
    @5
    @7
    @1
    @6
    caddc
    co
    cc0
    @5
    @6
    @1
    @5
    @1
    @5
    @1
    @9
    @1
    @17
    vz
    cz
    crab
    cE
    @17
    vz
    @1
    cz
    elrabi
    2zrng.e
    eleq2s
    zcnd
    #
    negcld
    @33
    addcomd
    @5
    @1
    @33
    negidd
    eqtrd
    rspcedvd
    rgen
    cE
    caddc
    vz
    cR
    cc0
    vy
    vx
    vz
    cR
    cE
    2zrng.e
    2zrngbas.r
    2zrngbas
    vx
    vz
    cR
    cE
    2zrng.e
    2zrngbas.r
    2zrngadd
    vx
    vz
    cR
    cE
    2zrng.e
    2zrngbas.r
    2zrng0
    isgrp
    mpbir2an
end

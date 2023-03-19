include "ccyg.mm"
include "wcel.mm"
include "cgrp.mm"
include "cv.mm"
include "cmg.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cz.mm"
include "wrex.mm"
include "cbs.mm"
include "wral.mm"
include "wa.mm"
include "cabl.mm"
include "eqid.mm"
include "iscyg3.mm"
include "cplusg.mm"
include "eqidd.mm"
include "simpll.mm"
include "wi.mm"
include "weq.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "rspccv.mm"
include "adantl.mm"
include "reeanv.mm"
include "caddc.mm"
include "cc.mm"
include "zcn.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "addcomd.mm"
include "oveq1d.mm"
include "simprl.mm"
include "simprr.mm"
include "simplr.mm"
include "mulgdir.mm"
include "syl13anc.mm"
include "3eqtr3d.mm"
include "oveq12.mm"
include "ancoms.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "adantr.mm"
include "syl2and.mm"
include "3impib.mm"
include "isabld.mm"
include "r19.29an.mm"
include "sylbi.mm"

theorem cygabl
  let cG: class G
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let vz: setvar z
  let cC: class C
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let cE: class E
  let cH: class H


  assert |- ( G e. CycGrp -> G e. Abel )

  proof
    cG
    ccyg
    wcel
    cG
    cgrp
    wcel
    #
    vy
    cv
    #
    vn
    cv
    #
    vx
    cv
    #
    cG
    cmg
    cfv
    #
    co
    #
    wceq
    #
    vn
    cz
    wrex
    #
    vy
    cG
    cbs
    cfv
    #
    wral
    #
    vx
    @8
    wrex
    wa
    cG
    cabl
    wcel
    #
    vx
    vy
    @8
    @4
    vn
    cG
    @8
    eqid
    #
    @4
    eqid
    #
    iscyg3
    @0
    @9
    @10
    vx
    @8
    @0
    @3
    @8
    wcel
    #
    wa
    #
    @9
    wa
    #
    va
    vb
    @8
    cG
    cplusg
    cfv
    #
    cG
    @15
    @8
    eqidd
    @15
    @16
    eqidd
    @0
    @13
    @9
    simpll
    @15
    va
    cv
    #
    @8
    wcel
    #
    vb
    cv
    #
    @8
    wcel
    #
    @17
    @19
    @16
    co
    #
    @19
    @17
    @16
    co
    #
    wceq
    #
    @15
    @18
    @17
    vm
    cv
    #
    @3
    @4
    co
    #
    wceq
    #
    vm
    cz
    wrex
    #
    @20
    @19
    @5
    wceq
    #
    vn
    cz
    wrex
    #
    @23
    @9
    @18
    @27
    wi
    @14
    @7
    @27
    vy
    @17
    @8
    vy
    va
    weq
    #
    @7
    @17
    @5
    wceq
    #
    vn
    cz
    wrex
    @27
    @30
    @6
    @31
    vn
    cz
    @1
    @17
    @5
    eqeq1
    rexbidv
    @31
    @26
    vn
    vm
    cz
    vn
    vm
    weq
    @5
    @25
    @17
    @2
    @24
    @3
    @4
    oveq1
    eqeq2d
    cbvrexv
    syl6bb
    rspccv
    adantl
    @9
    @20
    @29
    wi
    @14
    @7
    @29
    vy
    @19
    @8
    vy
    vb
    weq
    @6
    @28
    vn
    cz
    @1
    @19
    @5
    eqeq1
    rexbidv
    rspccv
    adantl
    @14
    @27
    @29
    wa
    #
    @23
    wi
    @9
    @32
    @26
    @28
    wa
    #
    vn
    cz
    wrex
    vm
    cz
    wrex
    @14
    @23
    @26
    @28
    vm
    vn
    cz
    cz
    reeanv
    @14
    @33
    @23
    vm
    vn
    cz
    cz
    @14
    @24
    cz
    wcel
    #
    @2
    cz
    wcel
    #
    wa
    #
    wa
    #
    @23
    @33
    @25
    @5
    @16
    co
    #
    @5
    @25
    @16
    co
    #
    wceq
    @37
    @24
    @2
    caddc
    co
    #
    @3
    @4
    co
    #
    @2
    @24
    caddc
    co
    #
    @3
    @4
    co
    #
    @38
    @39
    @37
    @40
    @42
    @3
    @4
    @37
    @24
    @2
    @34
    @24
    cc
    wcel
    @14
    @35
    @24
    zcn
    ad2antrl
    @35
    @2
    cc
    wcel
    @14
    @34
    @2
    zcn
    ad2antll
    addcomd
    oveq1d
    @37
    @0
    @34
    @35
    @13
    @41
    @38
    wceq
    @0
    @13
    @36
    simpll
    #
    @14
    @34
    @35
    simprl
    #
    @14
    @34
    @35
    simprr
    #
    @0
    @13
    @36
    simplr
    #
    @8
    @16
    @4
    cG
    @24
    @2
    @3
    @11
    @12
    @16
    eqid
    #
    mulgdir
    syl13anc
    @37
    @0
    @35
    @34
    @13
    @43
    @39
    wceq
    @44
    @46
    @45
    @47
    @8
    @16
    @4
    cG
    @2
    @24
    @3
    @11
    @12
    @48
    mulgdir
    syl13anc
    3eqtr3d
    @33
    @21
    @38
    @22
    @39
    @17
    @25
    @19
    @5
    @16
    oveq12
    @28
    @26
    @22
    @39
    wceq
    @19
    @5
    @17
    @25
    @16
    oveq12
    ancoms
    eqeq12d
    syl5ibrcom
    rexlimdvva
    syl5bir
    adantr
    syl2and
    3impib
    isabld
    r19.29an
    sylbi
end

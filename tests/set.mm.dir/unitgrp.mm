include "crg.mm"
include "wcel.mm"
include "cmulr.mm"
include "cfv.mm"
include "cur.mm"
include "cbs.mm"
include "wceq.mm"
include "unitgrpbas.mm"
include "a1i.mm"
include "cvv.mm"
include "cplusg.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cmgp.mm"
include "eqid.mm"
include "mgpplusg.mm"
include "ressplusg.mm"
include "mp1i.mm"
include "cv.mm"
include "unitmulcl.mm"
include "w3a.mm"
include "co.mm"
include "unitcl.mm"
include "3anim123i.mm"
include "ringass.mm"
include "sylan2.mm"
include "1unit.mm"
include "ringlidm.mm"
include "wa.mm"
include "cdsr.mm"
include "wbr.mm"
include "coppr.mm"
include "wrex.mm"
include "simpr.mm"
include "isunit.mm"
include "sylib.mm"
include "wb.mm"
include "adantl.mm"
include "dvdsr2.mm"
include "syl.mm"
include "opprbas.mm"
include "anbi12d.mm"
include "reeanv.mm"
include "simprl.mm"
include "ad2antrr.mm"
include "dvdsrmul.mm"
include "syl2anc.mm"
include "simplll.mm"
include "simplr.mm"
include "syl13anc.mm"
include "simprrl.mm"
include "oveq1d.mm"
include "opprmul.mm"
include "simprrr.mm"
include "syl5eqr.mm"
include "oveq2d.mm"
include "3eqtr3d.mm"
include "ringridm.mm"
include "3brtr3d.mm"
include "syl5eq.mm"
include "breqtrd.mm"
include "sylanbrc.mm"
include "jca.mm"
include "rexlimdvaa.mm"
include "expimpd.mm"
include "reximdv2.mm"
include "syl5bir.mm"
include "sylbid.mm"
include "mpd.mm"
include "isgrpde.mm"

theorem unitgrp
  let cR: class R
  let cU: class U
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  assume unitmulcl.1: |- U = ( Unit ` R )
  assume unitgrp.2: |- G = ( ( mulGrp ` R ) |`s U )


  assert |- ( R e. Ring -> G e. Grp )

  proof
    cR
    crg
    wcel
    #
    vx
    vy
    vz
    cU
    cR
    cmulr
    cfv
    #
    cG
    cR
    cur
    cfv
    #
    cU
    cG
    cbs
    cfv
    #
    wceq
    @0
    cR
    cU
    cG
    unitmulcl.1
    unitgrp.2
    unitgrpbas
    #
    a1i
    cU
    cvv
    wcel
    @1
    cG
    cplusg
    cfv
    wceq
    @0
    cU
    @3
    cvv
    @4
    cG
    cbs
    fvex
    eqeltri
    cU
    @1
    cR
    cmgp
    cfv
    #
    cG
    cvv
    unitgrp.2
    cR
    @1
    @5
    @5
    eqid
    @1
    eqid
    #
    mgpplusg
    ressplusg
    mp1i
    cR
    @1
    cU
    vx
    cv
    #
    vy
    cv
    #
    unitmulcl.1
    @6
    unitmulcl
    @7
    cU
    wcel
    #
    @8
    cU
    wcel
    #
    vz
    cv
    #
    cU
    wcel
    #
    w3a
    @0
    @7
    cR
    cbs
    cfv
    #
    wcel
    #
    @8
    @13
    wcel
    #
    @11
    @13
    wcel
    #
    w3a
    @7
    @8
    @1
    co
    @11
    @1
    co
    @7
    @8
    @11
    @1
    co
    @1
    co
    wceq
    @9
    @14
    @10
    @15
    @12
    @16
    @13
    cR
    cU
    @7
    @13
    eqid
    #
    unitmulcl.1
    unitcl
    #
    @13
    cR
    cU
    @8
    @17
    unitmulcl.1
    unitcl
    @13
    cR
    cU
    @11
    @17
    unitmulcl.1
    unitcl
    3anim123i
    @13
    cR
    @1
    @7
    @8
    @11
    @17
    @6
    ringass
    sylan2
    cR
    cU
    @2
    unitmulcl.1
    @2
    eqid
    #
    1unit
    @9
    @0
    @14
    @2
    @7
    @1
    co
    @7
    wceq
    @18
    @13
    cR
    @1
    @2
    @7
    @17
    @6
    @19
    ringlidm
    sylan2
    @0
    @9
    wa
    #
    @7
    @2
    cR
    cdsr
    cfv
    #
    wbr
    #
    @7
    @2
    cR
    coppr
    cfv
    #
    cdsr
    cfv
    #
    wbr
    #
    wa
    #
    @8
    @7
    @1
    co
    #
    @2
    wceq
    #
    vy
    cU
    wrex
    #
    @20
    @9
    @26
    @0
    @9
    simpr
    @21
    cR
    @23
    cU
    @2
    @24
    @7
    unitmulcl.1
    @19
    @21
    eqid
    #
    @23
    eqid
    #
    @24
    eqid
    #
    isunit
    sylib
    @20
    @26
    @28
    vy
    @13
    wrex
    #
    vm
    cv
    #
    @7
    @23
    cmulr
    cfv
    #
    co
    #
    @2
    wceq
    #
    vm
    @13
    wrex
    #
    wa
    #
    @29
    @20
    @22
    @33
    @25
    @38
    @20
    @14
    @22
    @33
    wb
    @9
    @14
    @0
    @18
    adantl
    #
    vy
    @13
    @21
    cR
    @1
    @7
    @2
    @17
    @30
    @6
    dvdsr2
    syl
    @20
    @14
    @25
    @38
    wb
    @40
    vm
    @13
    @24
    @23
    @35
    @7
    @2
    @13
    cR
    @23
    @31
    @17
    opprbas
    #
    @32
    @35
    eqid
    #
    dvdsr2
    syl
    anbi12d
    @39
    @28
    @37
    wa
    #
    vm
    @13
    wrex
    #
    vy
    @13
    wrex
    @20
    @29
    @28
    @37
    vy
    vm
    @13
    @13
    reeanv
    @20
    @44
    @28
    vy
    @13
    cU
    @20
    @15
    @44
    @10
    @28
    wa
    #
    @20
    @15
    wa
    #
    @43
    @45
    vm
    @13
    @46
    @34
    @13
    wcel
    #
    @43
    wa
    #
    wa
    #
    @10
    @28
    @49
    @8
    @2
    @21
    wbr
    @8
    @2
    @24
    wbr
    @10
    @49
    @34
    @7
    @34
    @1
    co
    #
    @8
    @2
    @21
    @49
    @47
    @14
    @34
    @50
    @21
    wbr
    @46
    @47
    @43
    simprl
    #
    @20
    @14
    @15
    @48
    @40
    ad2antrr
    #
    @13
    @21
    cR
    @1
    @34
    @7
    @17
    @30
    @6
    dvdsrmul
    syl2anc
    @49
    @2
    @34
    @1
    co
    #
    @8
    @2
    @1
    co
    #
    @34
    @8
    @49
    @27
    @34
    @1
    co
    #
    @8
    @50
    @1
    co
    #
    @53
    @54
    @49
    @0
    @15
    @14
    @47
    @55
    @56
    wceq
    @0
    @9
    @15
    @48
    simplll
    #
    @20
    @15
    @48
    simplr
    #
    @52
    @51
    @13
    cR
    @1
    @8
    @7
    @34
    @17
    @6
    ringass
    syl13anc
    @49
    @27
    @2
    @34
    @1
    @46
    @47
    @28
    @37
    simprrl
    #
    oveq1d
    @49
    @50
    @2
    @8
    @1
    @49
    @50
    @36
    @2
    @13
    cR
    @35
    @1
    @23
    @34
    @7
    @17
    @6
    @31
    @42
    opprmul
    @46
    @47
    @28
    @37
    simprrr
    syl5eqr
    #
    oveq2d
    3eqtr3d
    @49
    @0
    @47
    @53
    @34
    wceq
    @57
    @51
    @13
    cR
    @1
    @2
    @34
    @17
    @6
    @19
    ringlidm
    syl2anc
    @49
    @0
    @15
    @54
    @8
    wceq
    @57
    @58
    @13
    cR
    @1
    @2
    @8
    @17
    @6
    @19
    ringridm
    syl2anc
    3eqtr3d
    @60
    3brtr3d
    @49
    @8
    @7
    @8
    @35
    co
    #
    @2
    @24
    @49
    @15
    @14
    @8
    @61
    @24
    wbr
    @58
    @52
    @13
    @24
    @23
    @35
    @8
    @7
    @41
    @32
    @42
    dvdsrmul
    syl2anc
    @49
    @61
    @27
    @2
    @13
    cR
    @35
    @1
    @23
    @7
    @8
    @17
    @6
    @31
    @42
    opprmul
    @59
    syl5eq
    breqtrd
    @21
    cR
    @23
    cU
    @2
    @24
    @8
    unitmulcl.1
    @19
    @30
    @31
    @32
    isunit
    sylanbrc
    @59
    jca
    rexlimdvaa
    expimpd
    reximdv2
    syl5bir
    sylbid
    mpd
    isgrpde
end

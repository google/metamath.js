include "cc0.mm"
include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "0re.mm"
include "ax-rnegex.mm"
include "wa.mm"
include "wi.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "biimpd.mm"
include "adantld.mm"
include "wne.mm"
include "cmul.mm"
include "c1.mm"
include "ax-rrecex.mm"
include "adantlr.mm"
include "cc.mm"
include "simplll.mm"
include "recnd.mm"
include "simprl.mm"
include "0cn.mm"
include "mulass.mm"
include "mp3an3.mm"
include "syl2anc.mm"
include "oveq1.mm"
include "mulid2i.mm"
include "syl6eq.mm"
include "ad2antll.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "simpllr.mm"
include "remulcl.mm"
include "mpan2.mm"
include "ad2antrl.mm"
include "adddir.mm"
include "mp3an1.mm"
include "sylancr.mm"
include "addass.mm"
include "eqtr2d.mm"
include "wb.mm"
include "sylan2.mm"
include "readdcl.mm"
include "sylancl.mm"
include "readdcan.mm"
include "mp3an2.mm"
include "mpbid.mm"
include "rexlimddv.mm"
include "expcom.mm"
include "pm2.61ine.mm"
include "rexlimiva.mm"
include "mp2b.mm"

theorem 00id
  let vc: setvar c
  let vy: setvar y


  assert |- ( 0 + 0 ) = 0

  proof
    cc0
    cr
    wcel
    #
    cc0
    vc
    cv
    #
    caddc
    co
    #
    cc0
    wceq
    #
    vc
    cr
    wrex
    cc0
    cc0
    caddc
    co
    #
    cc0
    wceq
    #
    0re
    vc
    cc0
    ax-rnegex
    @3
    @5
    vc
    cr
    @1
    cr
    wcel
    #
    @3
    wa
    #
    @5
    wi
    @1
    cc0
    @1
    cc0
    wceq
    #
    @3
    @5
    @6
    @8
    @3
    @5
    @8
    @2
    @4
    cc0
    @1
    cc0
    cc0
    caddc
    oveq2
    eqeq1d
    biimpd
    adantld
    @7
    @1
    cc0
    wne
    #
    @5
    @7
    @9
    wa
    #
    @1
    vy
    cv
    #
    cmul
    co
    #
    c1
    wceq
    #
    @5
    vy
    cr
    @6
    @9
    @13
    vy
    cr
    wrex
    @3
    vy
    @1
    ax-rrecex
    adantlr
    @10
    @11
    cr
    wcel
    #
    @13
    wa
    #
    wa
    #
    @1
    @11
    cc0
    cmul
    co
    #
    cmul
    co
    #
    cc0
    caddc
    co
    #
    @4
    cc0
    @16
    @18
    cc0
    cc0
    caddc
    @16
    @12
    cc0
    cmul
    co
    #
    @18
    cc0
    @16
    @1
    cc
    wcel
    #
    @11
    cc
    wcel
    #
    @20
    @18
    wceq
    #
    @16
    @1
    @6
    @3
    @9
    @15
    simplll
    #
    recnd
    #
    @16
    @11
    @10
    @14
    @13
    simprl
    #
    recnd
    @21
    @22
    cc0
    cc
    wcel
    #
    @23
    0cn
    @1
    @11
    cc0
    mulass
    mp3an3
    syl2anc
    @13
    @20
    cc0
    wceq
    @10
    @14
    @13
    @20
    c1
    cc0
    cmul
    co
    cc0
    @12
    c1
    cc0
    cmul
    oveq1
    cc0
    0cn
    mulid2i
    syl6eq
    ad2antll
    eqtr3d
    oveq1d
    @16
    cc0
    @17
    cmul
    co
    #
    @19
    caddc
    co
    #
    @28
    cc0
    caddc
    co
    #
    wceq
    #
    @19
    cc0
    wceq
    #
    @16
    @30
    @28
    @18
    caddc
    co
    #
    cc0
    caddc
    co
    #
    @29
    @16
    @28
    @33
    cc0
    caddc
    @16
    @2
    @17
    cmul
    co
    #
    @28
    @33
    @16
    @2
    cc0
    @17
    cmul
    @6
    @3
    @9
    @15
    simpllr
    oveq1d
    @16
    @21
    @17
    cc
    wcel
    #
    @35
    @33
    wceq
    #
    @25
    @16
    @17
    @14
    @17
    cr
    wcel
    #
    @10
    @13
    @14
    @0
    @38
    0re
    @11
    cc0
    remulcl
    mpan2
    #
    ad2antrl
    #
    recnd
    @27
    @21
    @36
    @37
    0cn
    cc0
    @1
    @17
    adddir
    mp3an1
    syl2anc
    eqtr3d
    oveq1d
    @16
    @28
    cc
    wcel
    #
    @18
    cc
    wcel
    #
    @34
    @29
    wceq
    #
    @16
    @28
    @14
    @28
    cr
    wcel
    #
    @10
    @13
    @14
    @0
    @38
    @44
    0re
    @39
    cc0
    @17
    remulcl
    sylancr
    ad2antrl
    #
    recnd
    @16
    @18
    @16
    @6
    @38
    @18
    cr
    wcel
    #
    @24
    @40
    @1
    @17
    remulcl
    #
    syl2anc
    recnd
    @41
    @42
    @27
    @43
    0cn
    @28
    @18
    cc0
    addass
    mp3an3
    syl2anc
    eqtr2d
    @16
    @19
    cr
    wcel
    #
    @44
    @31
    @32
    wb
    #
    @16
    @6
    @14
    @48
    @24
    @26
    @6
    @14
    wa
    @46
    @0
    @48
    @14
    @6
    @38
    @46
    @39
    @47
    sylan2
    0re
    @18
    cc0
    readdcl
    sylancl
    syl2anc
    @45
    @48
    @0
    @44
    @49
    0re
    @19
    cc0
    @28
    readdcan
    mp3an2
    syl2anc
    mpbid
    eqtr3d
    rexlimddv
    expcom
    pm2.61ine
    rexlimiva
    mp2b
end

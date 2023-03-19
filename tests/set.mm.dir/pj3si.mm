include "cpjh.mm"
include "cfv.mm"
include "ccom.mm"
include "wceq.mm"
include "crn.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "cin.mm"
include "chil.mm"
include "wral.mm"
include "wcel.mm"
include "cmv.mm"
include "co.mm"
include "cva.mm"
include "cort.mm"
include "pj2cocli.mm"
include "adantl.mm"
include "wfn.mm"
include "pjfi.mm"
include "hocofi.mm"
include "hocofni.mm"
include "fnfvelrn.mm"
include "mpan.mm"
include "ssel.mm"
include "syl5.mm"
include "imp.mm"
include "elind.mm"
include "adantll.mm"
include "fveq1.mm"
include "eleq1d.mm"
include "syl5ibr.mm"
include "adantlr.mm"
include "csp.mm"
include "cc0.mm"
include "hococli.mm"
include "hvsubcl.mm"
include "mpdan.mm"
include "cmin.mm"
include "w3a.mm"
include "simpl.mm"
include "adantr.mm"
include "chincli.mm"
include "cheli.mm"
include "3jca.mm"
include "his2sub.mm"
include "syl.mm"
include "oveq1d.mm"
include "pjadj2coi.mm"
include "sylan2.mm"
include "pj3lem1.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "sylan9eq.mm"
include "cc.mm"
include "anim12i.mm"
include "hicl.mm"
include "subidd.mm"
include "3eqtr2d.mm"
include "expr.mm"
include "ralrimiv.mm"
include "csh.mm"
include "wb.mm"
include "chshii.mm"
include "shocel.mm"
include "ax-mp.mm"
include "sylanbrc.mm"
include "pjvi.mm"
include "syl2anc.mm"
include "id.mm"
include "hvaddsub12.mm"
include "syl3anc.mm"
include "c0v.mm"
include "hvsubid.mm"
include "ax-hvaddid.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "ralrimiva.mm"
include "hoeqi.mm"
include "sylib.mm"

theorem pj3si
  let cF: class F
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume pjadj2co.1: |- F e. CH
  assume pjadj2co.2: |- G e. CH
  assume pjadj2co.3: |- H e. CH


  assert |- ( ( ( ( ( projh ` F ) o. ( projh ` G ) ) o. ( projh ` H ) ) = ( ( ( projh ` H ) o. ( projh ` G ) ) o. ( projh ` F ) ) /\ ran ( ( ( projh ` F ) o. ( projh ` G ) ) o. ( projh ` H ) ) C_ G ) -> ( ( ( projh ` F ) o. ( projh ` G ) ) o. ( projh ` H ) ) = ( projh ` ( ( F i^i G ) i^i H ) ) )

  proof
    cF
    cpjh
    cfv
    #
    cG
    cpjh
    cfv
    #
    ccom
    #
    cH
    cpjh
    cfv
    #
    ccom
    #
    @3
    @1
    ccom
    @0
    ccom
    #
    wceq
    #
    @4
    crn
    #
    cG
    wss
    #
    wa
    #
    vx
    cv
    #
    @4
    cfv
    #
    @10
    cF
    cG
    cin
    #
    cH
    cin
    #
    cpjh
    cfv
    #
    cfv
    #
    wceq
    #
    vx
    chil
    wral
    @4
    @14
    wceq
    @9
    @16
    vx
    chil
    @9
    @10
    chil
    wcel
    #
    wa
    #
    @11
    @10
    @11
    cmv
    co
    #
    cva
    co
    #
    @14
    cfv
    #
    @11
    @15
    @18
    @11
    @13
    wcel
    @19
    @13
    cort
    cfv
    wcel
    #
    @21
    @11
    wceq
    @18
    @12
    cH
    @11
    @8
    @17
    @11
    @12
    wcel
    @6
    @8
    @17
    wa
    cF
    cG
    @11
    @17
    @11
    cF
    wcel
    @8
    @10
    cF
    cG
    cH
    pjadj2co.1
    pjadj2co.2
    pjadj2co.3
    pj2cocli
    adantl
    @8
    @17
    @11
    cG
    wcel
    #
    @17
    @11
    @7
    wcel
    #
    @8
    @23
    @4
    chil
    wfn
    @17
    @24
    @2
    @3
    @0
    @1
    cF
    pjadj2co.1
    pjfi
    cG
    pjadj2co.2
    pjfi
    hocofi
    #
    cH
    pjadj2co.3
    pjfi
    #
    hocofni
    chil
    @10
    @4
    fnfvelrn
    mpan
    @7
    cG
    @11
    ssel
    syl5
    imp
    elind
    adantll
    @6
    @17
    @11
    cH
    wcel
    #
    @8
    @6
    @17
    @27
    @17
    @27
    @6
    @10
    @5
    cfv
    #
    cH
    wcel
    @10
    cH
    cG
    cF
    pjadj2co.3
    pjadj2co.2
    pjadj2co.1
    pj2cocli
    @6
    @11
    @28
    cH
    @10
    @4
    @5
    fveq1
    #
    eleq1d
    syl5ibr
    imp
    adantlr
    elind
    @18
    @19
    chil
    wcel
    #
    @19
    vy
    cv
    #
    csp
    co
    #
    cc0
    wceq
    #
    vy
    @13
    wral
    #
    @22
    @17
    @30
    @9
    @17
    @11
    chil
    wcel
    #
    @30
    @10
    @2
    @3
    @25
    @26
    hococli
    #
    @10
    @11
    hvsubcl
    mpdan
    adantl
    @18
    @33
    vy
    @13
    @9
    @17
    @31
    @13
    wcel
    #
    @33
    @9
    @17
    @37
    wa
    #
    wa
    #
    @32
    @10
    @31
    csp
    co
    #
    @11
    @31
    csp
    co
    #
    cmin
    co
    #
    @41
    @41
    cmin
    co
    cc0
    @39
    @17
    @35
    @31
    chil
    wcel
    #
    w3a
    #
    @32
    @42
    wceq
    @38
    @44
    @9
    @38
    @17
    @35
    @43
    @17
    @37
    simpl
    @17
    @35
    @37
    @36
    adantr
    @37
    @43
    @17
    @31
    @13
    @12
    cH
    cF
    cG
    pjadj2co.1
    pjadj2co.2
    chincli
    pjadj2co.3
    chincli
    #
    cheli
    #
    adantl
    3jca
    adantl
    @10
    @11
    @31
    his2sub
    syl
    @39
    @41
    @40
    @41
    cmin
    @9
    @38
    @41
    @28
    @31
    csp
    co
    #
    @40
    @9
    @11
    @28
    @31
    csp
    @6
    @11
    @28
    wceq
    @8
    @29
    adantr
    oveq1d
    @38
    @47
    @10
    @31
    @4
    cfv
    #
    csp
    co
    #
    @40
    @37
    @17
    @43
    @47
    @49
    wceq
    @46
    @10
    @31
    cH
    cG
    cF
    pjadj2co.3
    pjadj2co.2
    pjadj2co.1
    pjadj2coi
    sylan2
    @37
    @49
    @40
    wceq
    @17
    @37
    @48
    @31
    @10
    csp
    @31
    cF
    cG
    cH
    pjadj2co.1
    pjadj2co.2
    pjadj2co.3
    pj3lem1
    oveq2d
    adantl
    eqtrd
    sylan9eq
    oveq1d
    @39
    @41
    @39
    @35
    @43
    wa
    #
    @41
    cc
    wcel
    @38
    @50
    @9
    @17
    @35
    @37
    @43
    @36
    @46
    anim12i
    adantl
    @11
    @31
    hicl
    syl
    subidd
    3eqtr2d
    expr
    ralrimiv
    @13
    csh
    wcel
    @22
    @30
    @34
    wa
    wb
    @13
    @45
    chshii
    vy
    @19
    @13
    shocel
    ax-mp
    sylanbrc
    @11
    @19
    @13
    @45
    pjvi
    syl2anc
    @17
    @21
    @15
    wceq
    @9
    @17
    @20
    @10
    @14
    @17
    @20
    @10
    @11
    @11
    cmv
    co
    #
    cva
    co
    #
    @10
    @17
    @35
    @17
    @35
    @20
    @52
    wceq
    @36
    @17
    id
    @36
    @11
    @10
    @11
    hvaddsub12
    syl3anc
    @17
    @52
    @10
    c0v
    cva
    co
    @10
    @17
    @51
    c0v
    @10
    cva
    @17
    @35
    @51
    c0v
    wceq
    @36
    @11
    hvsubid
    syl
    oveq2d
    @10
    ax-hvaddid
    eqtrd
    eqtrd
    fveq2d
    adantl
    eqtr3d
    ralrimiva
    vx
    @4
    @14
    @2
    @3
    @25
    @26
    hocofi
    @13
    @45
    pjfi
    hoeqi
    sylib
end

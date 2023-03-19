include "cpjh.mm"
include "cfv.mm"
include "ccom.mm"
include "wceq.mm"
include "cv.mm"
include "cin.mm"
include "chil.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cmv.mm"
include "co.mm"
include "cva.mm"
include "cort.mm"
include "pjcocli.mm"
include "adantl.mm"
include "fveq1.mm"
include "eleq1d.mm"
include "syl5ibr.mm"
include "imp.mm"
include "elind.mm"
include "csp.mm"
include "cc0.mm"
include "pjcohcli.mm"
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
include "pjadjcoi.mm"
include "sylan2.mm"
include "pjclem4a.mm"
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
include "c0v.mm"
include "id.mm"
include "hvaddsub12.mm"
include "syl3anc.mm"
include "hvsubid.mm"
include "ax-hvaddid.mm"
include "3eqtrd.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "ralrimiva.mm"
include "pjfi.mm"
include "hocofi.mm"
include "hoeqi.mm"
include "sylib.mm"

theorem pjclem4
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume pjclem1.1: |- G e. CH
  assume pjclem1.2: |- H e. CH


  assert |- ( ( ( projh ` G ) o. ( projh ` H ) ) = ( ( projh ` H ) o. ( projh ` G ) ) -> ( ( projh ` G ) o. ( projh ` H ) ) = ( projh ` ( G i^i H ) ) )

  proof
    cG
    cpjh
    cfv
    #
    cH
    cpjh
    cfv
    #
    ccom
    #
    @1
    @0
    ccom
    #
    wceq
    #
    vx
    cv
    #
    @2
    cfv
    #
    @5
    cG
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
    @2
    @8
    wceq
    @4
    @10
    vx
    chil
    @4
    @5
    chil
    wcel
    #
    wa
    #
    @6
    @5
    @6
    cmv
    co
    #
    cva
    co
    #
    @8
    cfv
    #
    @6
    @9
    @12
    @6
    @7
    wcel
    @13
    @7
    cort
    cfv
    wcel
    #
    @15
    @6
    wceq
    @12
    cG
    cH
    @6
    @11
    @6
    cG
    wcel
    @4
    @5
    cG
    cH
    pjclem1.1
    pjclem1.2
    pjcocli
    adantl
    @4
    @11
    @6
    cH
    wcel
    #
    @11
    @17
    @4
    @5
    @3
    cfv
    #
    cH
    wcel
    @5
    cH
    cG
    pjclem1.2
    pjclem1.1
    pjcocli
    @4
    @6
    @18
    cH
    @5
    @2
    @3
    fveq1
    #
    eleq1d
    syl5ibr
    imp
    elind
    @12
    @13
    chil
    wcel
    #
    @13
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
    @7
    wral
    #
    @16
    @11
    @20
    @4
    @11
    @6
    chil
    wcel
    #
    @20
    @5
    cG
    cH
    pjclem1.1
    pjclem1.2
    pjcohcli
    #
    @5
    @6
    hvsubcl
    mpdan
    adantl
    @12
    @23
    vy
    @7
    @4
    @11
    @21
    @7
    wcel
    #
    @23
    @4
    @11
    @27
    wa
    #
    wa
    #
    @22
    @5
    @21
    csp
    co
    #
    @6
    @21
    csp
    co
    #
    cmin
    co
    #
    @31
    @31
    cmin
    co
    cc0
    @29
    @11
    @25
    @21
    chil
    wcel
    #
    w3a
    #
    @22
    @32
    wceq
    @28
    @34
    @4
    @28
    @11
    @25
    @33
    @11
    @27
    simpl
    @11
    @25
    @27
    @26
    adantr
    @27
    @33
    @11
    @21
    @7
    cG
    cH
    pjclem1.1
    pjclem1.2
    chincli
    #
    cheli
    #
    adantl
    3jca
    adantl
    @5
    @6
    @21
    his2sub
    syl
    @29
    @31
    @30
    @31
    cmin
    @4
    @28
    @31
    @18
    @21
    csp
    co
    #
    @30
    @4
    @6
    @18
    @21
    csp
    @19
    oveq1d
    @28
    @37
    @5
    @21
    @2
    cfv
    #
    csp
    co
    #
    @30
    @27
    @11
    @33
    @37
    @39
    wceq
    @36
    @5
    @21
    cH
    cG
    pjclem1.2
    pjclem1.1
    pjadjcoi
    sylan2
    @27
    @39
    @30
    wceq
    @11
    @27
    @38
    @21
    @5
    csp
    @21
    cG
    cH
    pjclem1.1
    pjclem1.2
    pjclem4a
    oveq2d
    adantl
    eqtrd
    sylan9eq
    oveq1d
    @29
    @31
    @29
    @25
    @33
    wa
    #
    @31
    cc
    wcel
    @28
    @40
    @4
    @11
    @25
    @27
    @33
    @26
    @36
    anim12i
    adantl
    @6
    @21
    hicl
    syl
    subidd
    3eqtr2d
    expr
    ralrimiv
    @7
    csh
    wcel
    @16
    @20
    @24
    wa
    wb
    @7
    @35
    chshii
    vy
    @13
    @7
    shocel
    ax-mp
    sylanbrc
    @6
    @13
    @7
    @35
    pjvi
    syl2anc
    @11
    @15
    @9
    wceq
    @4
    @11
    @14
    @5
    @8
    @11
    @14
    @5
    @6
    @6
    cmv
    co
    #
    cva
    co
    #
    @5
    c0v
    cva
    co
    @5
    @11
    @25
    @11
    @25
    @14
    @42
    wceq
    @26
    @11
    id
    @26
    @6
    @5
    @6
    hvaddsub12
    syl3anc
    @11
    @41
    c0v
    @5
    cva
    @11
    @25
    @41
    c0v
    wceq
    @26
    @6
    hvsubid
    syl
    oveq2d
    @5
    ax-hvaddid
    3eqtrd
    fveq2d
    adantl
    eqtr3d
    ralrimiva
    vx
    @2
    @8
    @0
    @1
    cG
    pjclem1.1
    pjfi
    cH
    pjclem1.2
    pjfi
    hocofi
    @7
    @35
    pjfi
    hoeqi
    sylib
end

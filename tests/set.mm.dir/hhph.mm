include "ccphlo.mm"
include "wcel.mm"
include "cva.mm"
include "csm.mm"
include "cop.mm"
include "cno.mm"
include "cnv.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "c1.mm"
include "cneg.mm"
include "caddc.mm"
include "cmul.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "eqid.mm"
include "hhnv.mm"
include "wa.mm"
include "cmv.mm"
include "normpar.mm"
include "hvsubval.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "cr.mm"
include "hvaddcl.mm"
include "normcl.mm"
include "syl.mm"
include "recnd.mm"
include "sqcld.mm"
include "cc.mm"
include "hvsubcl.mm"
include "addcomd.mm"
include "eqtr3d.mm"
include "2cn.mm"
include "adddi.mm"
include "mp3an1.mm"
include "syl2an.mm"
include "3eqtr4d.mm"
include "rgen2a.mm"
include "cvv.mm"
include "wb.mm"
include "cablo.mm"
include "hilablo.mm"
include "elexi.mm"
include "hvmulex.mm"
include "wf.mm"
include "normf.mm"
include "ax-hilex.mm"
include "fex.mm"
include "mp2an.mm"
include "w3a.mm"
include "eleq1i.mm"
include "cgr.mm"
include "ablogrpo.mm"
include "ax-mp.mm"
include "cxp.mm"
include "ax-hfvadd.mm"
include "fdmi.mm"
include "grporn.mm"
include "isphg.mm"
include "syl5bb.mm"
include "mp3an.mm"
include "mpbir2an.mm"

theorem hhph
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  assume hhnv.1: |- U = <. <. +h , .h >. , normh >.


  assert |- U e. CPreHilOLD

  proof
    cU
    ccphlo
    wcel
    #
    cva
    csm
    cop
    cno
    cop
    #
    cnv
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cva
    co
    #
    cno
    cfv
    #
    c2
    cexp
    co
    #
    @3
    c1
    cneg
    @4
    csm
    co
    cva
    co
    #
    cno
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    c2
    @3
    cno
    cfv
    #
    c2
    cexp
    co
    #
    @4
    cno
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    cmul
    co
    #
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    #
    @1
    @1
    eqid
    hhnv
    @17
    vx
    vy
    chil
    @3
    chil
    wcel
    #
    @4
    chil
    wcel
    #
    wa
    #
    @3
    @4
    cmv
    co
    #
    cno
    cfv
    #
    c2
    cexp
    co
    #
    @7
    caddc
    co
    #
    c2
    @13
    cmul
    co
    c2
    @15
    cmul
    co
    caddc
    co
    #
    @11
    @16
    @3
    @4
    normpar
    @21
    @7
    @24
    caddc
    co
    @11
    @25
    @21
    @24
    @10
    @7
    caddc
    @21
    @23
    @9
    c2
    cexp
    @21
    @22
    @8
    cno
    @3
    @4
    hvsubval
    fveq2d
    oveq1d
    oveq2d
    @21
    @7
    @24
    @21
    @6
    @21
    @6
    @21
    @5
    chil
    wcel
    @6
    cr
    wcel
    @3
    @4
    hvaddcl
    @5
    normcl
    syl
    recnd
    sqcld
    @21
    @23
    @21
    @22
    chil
    wcel
    #
    @23
    cc
    wcel
    @3
    @4
    hvsubcl
    @27
    @23
    @22
    normcl
    recnd
    syl
    sqcld
    addcomd
    eqtr3d
    @19
    @13
    cc
    wcel
    #
    @15
    cc
    wcel
    #
    @16
    @26
    wceq
    #
    @20
    @19
    @12
    @19
    @12
    @3
    normcl
    recnd
    sqcld
    @20
    @14
    @20
    @14
    @4
    normcl
    recnd
    sqcld
    c2
    cc
    wcel
    @28
    @29
    @30
    2cn
    c2
    @13
    @15
    adddi
    mp3an1
    syl2an
    3eqtr4d
    rgen2a
    cva
    cvv
    wcel
    #
    csm
    cvv
    wcel
    #
    cno
    cvv
    wcel
    #
    @0
    @2
    @18
    wa
    #
    wb
    cva
    cablo
    hilablo
    elexi
    hvmulex
    chil
    cr
    cno
    wf
    chil
    cvv
    wcel
    @33
    normf
    ax-hilex
    chil
    cr
    cvv
    cno
    fex
    mp2an
    @0
    @1
    ccphlo
    wcel
    @31
    @32
    @33
    w3a
    @34
    cU
    @1
    ccphlo
    hhnv.1
    eleq1i
    vx
    vy
    cvv
    cvv
    cvv
    csm
    cva
    cno
    chil
    cva
    chil
    cva
    cablo
    wcel
    cva
    cgr
    wcel
    hilablo
    cva
    ablogrpo
    ax-mp
    chil
    chil
    cxp
    chil
    cva
    ax-hfvadd
    fdmi
    grporn
    isphg
    syl5bb
    mp3an
    mpbir2an
end

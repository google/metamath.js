include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cmin.mm"
include "cmo.mm"
include "cdiv.mm"
include "cz.mm"
include "wrex.mm"
include "cioc.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "simpl.mm"
include "2re.mm"
include "pire.mm"
include "remulcli.mm"
include "readdcl.mm"
include "sylancl.mm"
include "crp.mm"
include "resubcl.mm"
include "2pos.mm"
include "pipos.mm"
include "mulgt0ii.mm"
include "elrpii.mm"
include "modcl.mm"
include "resubcld.mm"
include "a1i.mm"
include "modlt.mm"
include "ltadd2dd.mm"
include "ltaddsubd.mm"
include "mpbid.mm"
include "cc0.mm"
include "modge0.mm"
include "subge02d.mm"
include "cxr.mm"
include "w3a.mm"
include "wb.mm"
include "rexr.mm"
include "adantr.mm"
include "elioc2.mm"
include "syl2anc.mm"
include "mpbir3and.mm"
include "syl6eleqr.mm"
include "c1.mm"
include "cneg.mm"
include "cfl.mm"
include "cfv.mm"
include "wceq.mm"
include "modval.mm"
include "oveq2d.mm"
include "recnd.mm"
include "wne.mm"
include "gt0ne0ii.mm"
include "redivcl.mm"
include "mp3an23.mm"
include "syl.mm"
include "flcld.mm"
include "zred.mm"
include "remulcl.mm"
include "sylancr.mm"
include "subsubd.mm"
include "cc.mm"
include "recni.mm"
include "simpr.mm"
include "pnncand.mm"
include "oveq1d.mm"
include "3eqtrd.mm"
include "addcl.mm"
include "subsub4d.mm"
include "negsubdi2d.mm"
include "pncand.mm"
include "negeqd.mm"
include "eqtr3d.mm"
include "neg1cn.mm"
include "mulm1i.mm"
include "mulcomli.mm"
include "syl6eqr.mm"
include "zcnd.mm"
include "subdid.mm"
include "eqtr4d.mm"
include "3eqtr2d.mm"
include "neg1z.mm"
include "zsubcl.mm"
include "divcan3.mm"
include "eqtrd.mm"
include "eqeltrd.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "rspcev.mm"

theorem efif1olem2
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cD: class D
  assume efif1olem1.1: |- D = ( A (,] ( A + ( 2 x. _pi ) ) )

  disjoint y z
  disjoint A y
  disjoint D y
  assert |- ( ( A e. RR /\ z e. RR ) -> E. y e. D ( ( z - y ) / ( 2 x. _pi ) ) e. ZZ )

  proof
    cA
    cr
    wcel
    #
    vz
    cv
    #
    cr
    wcel
    #
    wa
    #
    cA
    c2
    cpi
    cmul
    co
    #
    caddc
    co
    #
    cA
    @1
    cmin
    co
    #
    @4
    cmo
    co
    #
    cmin
    co
    #
    cD
    wcel
    @1
    @8
    cmin
    co
    #
    @4
    cdiv
    co
    #
    cz
    wcel
    #
    @1
    vy
    cv
    #
    cmin
    co
    #
    @4
    cdiv
    co
    #
    cz
    wcel
    #
    vy
    cD
    wrex
    @3
    @8
    cA
    @5
    cioc
    co
    #
    cD
    @3
    @8
    @16
    wcel
    #
    @8
    cr
    wcel
    #
    cA
    @8
    clt
    wbr
    #
    @8
    @5
    cle
    wbr
    #
    @3
    @5
    @7
    @3
    @0
    @4
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    @0
    @2
    simpl
    #
    c2
    cpi
    2re
    pire
    remulcli
    #
    cA
    @4
    readdcl
    sylancl
    #
    @3
    @6
    cr
    wcel
    #
    @4
    crp
    wcel
    #
    @7
    cr
    wcel
    cA
    @1
    resubcl
    #
    @4
    @24
    c2
    cpi
    2re
    pire
    2pos
    pipos
    mulgt0ii
    #
    elrpii
    #
    @6
    @4
    modcl
    sylancl
    #
    resubcld
    @3
    cA
    @7
    caddc
    co
    @5
    clt
    wbr
    @19
    @3
    @7
    @4
    cA
    @31
    @21
    @3
    @24
    a1i
    @23
    @3
    @26
    @27
    @7
    @4
    clt
    wbr
    @28
    @30
    @6
    @4
    modlt
    sylancl
    ltadd2dd
    @3
    cA
    @7
    @5
    @23
    @31
    @25
    ltaddsubd
    mpbid
    @3
    cc0
    @7
    cle
    wbr
    #
    @20
    @3
    @26
    @27
    @32
    @28
    @30
    @6
    @4
    modge0
    sylancl
    @3
    @5
    @7
    @25
    @31
    subge02d
    mpbid
    @3
    cA
    cxr
    wcel
    #
    @22
    @17
    @18
    @19
    @20
    w3a
    wb
    @0
    @33
    @2
    cA
    rexr
    adantr
    @25
    cA
    @5
    @8
    elioc2
    syl2anc
    mpbir3and
    efif1olem1.1
    syl6eleqr
    @3
    @10
    c1
    cneg
    #
    @6
    @4
    cdiv
    co
    #
    cfl
    cfv
    #
    cmin
    co
    #
    cz
    @3
    @10
    @4
    @37
    cmul
    co
    #
    @4
    cdiv
    co
    #
    @37
    @3
    @9
    @38
    @4
    cdiv
    @3
    @9
    @1
    @4
    @1
    caddc
    co
    #
    @4
    @36
    cmul
    co
    #
    caddc
    co
    #
    cmin
    co
    @1
    @40
    cmin
    co
    #
    @41
    cmin
    co
    #
    @38
    @3
    @8
    @42
    @1
    cmin
    @3
    @8
    @5
    @6
    @41
    cmin
    co
    #
    cmin
    co
    @5
    @6
    cmin
    co
    #
    @41
    caddc
    co
    @42
    @3
    @7
    @45
    @5
    cmin
    @3
    @26
    @27
    @7
    @45
    wceq
    @28
    @30
    @6
    @4
    modval
    sylancl
    oveq2d
    @3
    @5
    @6
    @41
    @3
    @5
    @25
    recnd
    @3
    @6
    @28
    recnd
    @3
    @41
    @3
    @21
    @36
    cr
    wcel
    @41
    cr
    wcel
    @24
    @3
    @36
    @3
    @35
    @3
    @26
    @35
    cr
    wcel
    #
    @28
    @26
    @21
    @4
    cc0
    wne
    #
    @47
    @24
    @4
    @24
    @29
    gt0ne0ii
    #
    @6
    @4
    redivcl
    mp3an23
    syl
    flcld
    #
    zred
    @4
    @36
    remulcl
    sylancr
    recnd
    #
    subsubd
    @3
    @46
    @40
    @41
    caddc
    @3
    cA
    @4
    @1
    @3
    cA
    @23
    recnd
    @4
    cc
    wcel
    #
    @3
    @4
    @24
    recni
    #
    a1i
    #
    @3
    @1
    @0
    @2
    simpr
    recnd
    #
    pnncand
    oveq1d
    3eqtrd
    oveq2d
    @3
    @1
    @40
    @41
    @55
    @3
    @52
    @1
    cc
    wcel
    @40
    cc
    wcel
    @53
    @55
    @4
    @1
    addcl
    sylancr
    #
    @51
    subsub4d
    @3
    @44
    @4
    @34
    cmul
    co
    #
    @41
    cmin
    co
    @38
    @3
    @43
    @57
    @41
    cmin
    @3
    @43
    @4
    cneg
    #
    @57
    @3
    @40
    @1
    cmin
    co
    #
    cneg
    @43
    @58
    @3
    @40
    @1
    @56
    @55
    negsubdi2d
    @3
    @59
    @4
    @3
    @4
    @1
    @54
    @55
    pncand
    negeqd
    eqtr3d
    @34
    @4
    @58
    neg1cn
    @53
    @4
    @53
    mulm1i
    mulcomli
    syl6eqr
    oveq1d
    @3
    @4
    @34
    @36
    @54
    @34
    cc
    wcel
    @3
    neg1cn
    a1i
    @3
    @36
    @50
    zcnd
    subdid
    eqtr4d
    3eqtr2d
    oveq1d
    @3
    @37
    cc
    wcel
    #
    @39
    @37
    wceq
    #
    @3
    @37
    @3
    @34
    cz
    wcel
    @36
    cz
    wcel
    @37
    cz
    wcel
    neg1z
    @50
    @34
    @36
    zsubcl
    sylancr
    #
    zcnd
    @60
    @52
    @48
    @61
    @53
    @49
    @37
    @4
    divcan3
    mp3an23
    syl
    eqtrd
    @62
    eqeltrd
    @15
    @11
    vy
    @8
    cD
    @12
    @8
    wceq
    #
    @14
    @10
    cz
    @63
    @13
    @9
    @4
    cdiv
    @12
    @8
    @1
    cmin
    oveq2
    oveq1d
    eleq1d
    rspcev
    syl2anc
end

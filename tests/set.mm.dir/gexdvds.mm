include "cgrp.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wi.mm"
include "gexdvdsi.mm"
include "3expia.mm"
include "ralrimdva.mm"
include "adantr.mm"
include "cc0.mm"
include "cn.mm"
include "crab.mm"
include "c0.mm"
include "cabs.mm"
include "cfv.mm"
include "wn.mm"
include "noel.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "elrab.mm"
include "simprr.mm"
include "eleq2d.mm"
include "syl5rbbr.mm"
include "rbaibd.mm"
include "mtbii.mm"
include "ex.mm"
include "cn0.mm"
include "wo.mm"
include "nn0abscl.mm"
include "ad2antlr.mm"
include "elnn0.mm"
include "sylib.mm"
include "ord.mm"
include "syld.mm"
include "wb.mm"
include "cneg.mm"
include "simpr.mm"
include "oveq1d.mm"
include "cminusg.mm"
include "eqid.mm"
include "mulgneg.mm"
include "3expa.mm"
include "grpinvid.mm"
include "ad2antrr.mm"
include "eqcomd.mm"
include "eqeq12d.mm"
include "simpll.mm"
include "mulgcl.mm"
include "grpidcl.mm"
include "grpinv11.mm"
include "bitrd.mm"
include "sylan9bbr.mm"
include "cr.mm"
include "zre.mm"
include "absord.mm"
include "mpjaodan.mm"
include "ralbidva.mm"
include "0dvds.mm"
include "simprl.mm"
include "breq1d.mm"
include "cc.mm"
include "zcn.mm"
include "abs00ad.mm"
include "3bitr4rd.mm"
include "3imtr3d.mm"
include "elrabi.mm"
include "cmo.mm"
include "cdiv.mm"
include "cfl.mm"
include "cmul.mm"
include "cmin.mm"
include "csg.mm"
include "crp.mm"
include "adantl.mm"
include "nnrp.mm"
include "modval.mm"
include "syl2an.mm"
include "simplll.mm"
include "simpllr.mm"
include "nnz.mm"
include "rerpdivcl.mm"
include "flcld.mm"
include "zmulcld.mm"
include "mulgsubdir.mm"
include "syl13anc.mm"
include "dvdsmul1.mm"
include "syl2anc.mm"
include "syl3anc.mm"
include "oveq12d.mm"
include "grpsubid.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "expr.mm"
include "ralimdva.mm"
include "cle.mm"
include "clt.mm"
include "modlt.mm"
include "zmodcl.mm"
include "adantll.mm"
include "nn0red.mm"
include "nnre.mm"
include "ltnled.mm"
include "mpbid.mm"
include "w3a.mm"
include "c1.mm"
include "cfz.mm"
include "gexlem2.mm"
include "elfzle2.mm"
include "syl.mm"
include "impancom.mm"
include "con3d.mm"
include "mpid.mm"
include "3syld.mm"
include "simplr.mm"
include "dvdsval3.mm"
include "sylibrd.mm"
include "sylan2.mm"
include "gexlem1.mm"
include "impbid.mm"

theorem gexdvds
  let vx: setvar x
  let c.x: class .x.
  let cE: class E
  let cG: class G
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let cA: class A
  let vy: setvar y
  let cV: class V
  assume gexcl.1: |- X = ( Base ` G )
  assume gexcl.2: |- E = ( gEx ` G )
  assume gexid.3: |- .x. = ( .g ` G )
  assume gexid.4: |- .0. = ( 0g ` G )

  disjoint E x
  disjoint G x
  disjoint N x
  disjoint X x
  disjoint .0. x
  disjoint .x. x
  disjoint A x
  disjoint x y
  disjoint E y
  disjoint G y
  disjoint N y
  disjoint V x
  disjoint V y
  disjoint X y
  disjoint .0. y
  disjoint .x. y
  assert |- ( ( G e. Grp /\ N e. ZZ ) -> ( E || N <-> A. x e. X ( N .x. x ) = .0. ) )

  proof
    cG
    cgrp
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cE
    cN
    cdvds
    wbr
    #
    cN
    vx
    cv
    #
    c.x
    co
    #
    c.0
    wceq
    #
    vx
    cX
    wral
    #
    @0
    @3
    @7
    wi
    @1
    @0
    @3
    @6
    vx
    cX
    @0
    @4
    cX
    wcel
    #
    @3
    @6
    @4
    c.x
    cE
    cG
    cN
    cX
    c.0
    gexcl.1
    gexcl.2
    gexid.3
    gexid.4
    gexdvdsi
    3expia
    ralrimdva
    adantr
    @2
    cE
    cc0
    wceq
    #
    vy
    cv
    #
    @4
    c.x
    co
    #
    c.0
    wceq
    #
    vx
    cX
    wral
    #
    vy
    cn
    crab
    #
    c0
    wceq
    #
    wa
    #
    @7
    @3
    wi
    #
    cE
    @14
    wcel
    #
    @2
    @16
    wa
    #
    cN
    cabs
    cfv
    #
    @4
    c.x
    co
    #
    c.0
    wceq
    #
    vx
    cX
    wral
    #
    @20
    cc0
    wceq
    #
    @7
    @3
    @19
    @23
    @20
    cn
    wcel
    #
    wn
    #
    @24
    @19
    @23
    @26
    @19
    @23
    wa
    @20
    c0
    wcel
    #
    @25
    @20
    noel
    @19
    @27
    @25
    @23
    @25
    @23
    wa
    @20
    @14
    wcel
    @19
    @27
    @13
    @23
    vy
    @20
    cn
    @10
    @20
    wceq
    #
    @12
    @22
    vx
    cX
    @28
    @11
    @21
    c.0
    @10
    @20
    @4
    c.x
    oveq1
    eqeq1d
    ralbidv
    elrab
    @19
    @14
    c0
    @20
    @2
    @9
    @15
    simprr
    eleq2d
    syl5rbbr
    rbaibd
    mtbii
    ex
    @19
    @25
    @24
    @19
    @20
    cn0
    wcel
    #
    @25
    @24
    wo
    @1
    @29
    @0
    @16
    cN
    nn0abscl
    ad2antlr
    @20
    elnn0
    sylib
    ord
    syld
    @2
    @23
    @7
    wb
    @16
    @2
    @22
    @6
    vx
    cX
    @2
    @8
    wa
    #
    @20
    cN
    wceq
    #
    @22
    @6
    wb
    @20
    cN
    cneg
    #
    wceq
    #
    @30
    @31
    wa
    #
    @21
    @5
    c.0
    @34
    @20
    cN
    @4
    c.x
    @30
    @31
    simpr
    oveq1d
    eqeq1d
    @33
    @22
    @32
    @4
    c.x
    co
    #
    c.0
    wceq
    #
    @30
    @6
    @33
    @21
    @35
    c.0
    @20
    @32
    @4
    c.x
    oveq1
    eqeq1d
    @30
    @36
    @5
    cG
    cminusg
    cfv
    #
    cfv
    #
    c.0
    @37
    cfv
    #
    wceq
    @6
    @30
    @35
    @38
    c.0
    @39
    @0
    @1
    @8
    @35
    @38
    wceq
    cX
    c.x
    cG
    @37
    cN
    @4
    gexcl.1
    gexid.3
    @37
    eqid
    #
    mulgneg
    3expa
    @30
    @39
    c.0
    @0
    @39
    c.0
    wceq
    @1
    @8
    cG
    @37
    c.0
    gexid.4
    @40
    grpinvid
    ad2antrr
    eqcomd
    eqeq12d
    @30
    cX
    cG
    @37
    @5
    c.0
    gexcl.1
    @40
    @0
    @1
    @8
    simpll
    @0
    @1
    @8
    @5
    cX
    wcel
    cX
    c.x
    cG
    cN
    @4
    gexcl.1
    gexid.3
    mulgcl
    3expa
    @0
    c.0
    cX
    wcel
    #
    @1
    @8
    cX
    cG
    c.0
    gexcl.1
    gexid.4
    grpidcl
    #
    ad2antrr
    grpinv11
    bitrd
    sylan9bbr
    @30
    cN
    @1
    cN
    cr
    wcel
    #
    @0
    @8
    cN
    zre
    #
    ad2antlr
    absord
    mpjaodan
    ralbidva
    adantr
    @19
    cc0
    cN
    cdvds
    wbr
    #
    cN
    cc0
    wceq
    #
    @3
    @24
    @1
    @45
    @46
    wb
    @0
    @16
    cN
    0dvds
    ad2antlr
    @19
    cE
    cc0
    cN
    cdvds
    @2
    @9
    @15
    simprl
    breq1d
    @19
    cN
    @1
    cN
    cc
    wcel
    @0
    @16
    cN
    zcn
    ad2antlr
    abs00ad
    3bitr4rd
    3imtr3d
    @18
    @2
    cE
    cn
    wcel
    #
    @17
    @13
    vy
    cE
    cn
    elrabi
    @2
    @47
    wa
    #
    @7
    cN
    cE
    cmo
    co
    #
    cc0
    wceq
    #
    @3
    @48
    @7
    @49
    @4
    c.x
    co
    #
    c.0
    wceq
    #
    vx
    cX
    wral
    #
    @49
    cn
    wcel
    #
    wn
    #
    @50
    @48
    @6
    @52
    vx
    cX
    @48
    @8
    @6
    @52
    @48
    @8
    @6
    wa
    #
    wa
    #
    @51
    cN
    cE
    cN
    cE
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    @4
    c.x
    co
    #
    @5
    @60
    @4
    c.x
    co
    #
    cG
    csg
    cfv
    #
    co
    #
    c.0
    @57
    @49
    @61
    @4
    c.x
    @48
    @49
    @61
    wceq
    #
    @56
    @2
    @43
    cE
    crp
    wcel
    #
    @66
    @47
    @1
    @43
    @0
    @44
    adantl
    #
    cE
    nnrp
    #
    cN
    cE
    modval
    syl2an
    adantr
    oveq1d
    @57
    @0
    @1
    @60
    cz
    wcel
    @8
    @62
    @65
    wceq
    @0
    @1
    @47
    @56
    simplll
    #
    @0
    @1
    @47
    @56
    simpllr
    @57
    cE
    @59
    @47
    cE
    cz
    wcel
    #
    @2
    @56
    cE
    nnz
    ad2antlr
    #
    @48
    @59
    cz
    wcel
    #
    @56
    @48
    @58
    @2
    @43
    @67
    @58
    cr
    wcel
    @47
    @68
    @69
    cN
    cE
    rerpdivcl
    syl2an
    flcld
    adantr
    #
    zmulcld
    @48
    @8
    @6
    simprl
    #
    cX
    c.x
    cG
    cN
    @64
    @60
    @4
    gexcl.1
    gexid.3
    @64
    eqid
    #
    mulgsubdir
    syl13anc
    @57
    @65
    c.0
    c.0
    @64
    co
    #
    c.0
    @57
    @5
    c.0
    @63
    c.0
    @64
    @48
    @8
    @6
    simprr
    @57
    @0
    @8
    cE
    @60
    cdvds
    wbr
    #
    @63
    c.0
    wceq
    @70
    @75
    @57
    @71
    @73
    @78
    @72
    @74
    cE
    @59
    dvdsmul1
    syl2anc
    @4
    c.x
    cE
    cG
    @60
    cX
    c.0
    gexcl.1
    gexcl.2
    gexid.3
    gexid.4
    gexdvdsi
    syl3anc
    oveq12d
    @48
    @77
    c.0
    wceq
    #
    @56
    @48
    @0
    @41
    @79
    @0
    @1
    @47
    simpll
    @0
    @41
    @1
    @47
    @42
    ad2antrr
    cX
    cG
    @64
    c.0
    c.0
    gexcl.1
    gexid.4
    @76
    grpsubid
    syl2anc
    adantr
    eqtrd
    3eqtrd
    expr
    ralimdva
    @48
    @53
    cE
    @49
    cle
    wbr
    #
    wn
    #
    @55
    @48
    @49
    cE
    clt
    wbr
    #
    @81
    @2
    @43
    @67
    @82
    @47
    @68
    @69
    cN
    cE
    modlt
    syl2an
    @48
    @49
    cE
    @48
    @49
    @1
    @47
    @49
    cn0
    wcel
    #
    @0
    cN
    cE
    zmodcl
    adantll
    #
    nn0red
    @47
    cE
    cr
    wcel
    @2
    cE
    nnre
    adantl
    ltnled
    mpbid
    @0
    @53
    @81
    @55
    wi
    #
    wi
    @1
    @47
    @0
    @53
    @85
    @0
    @53
    wa
    @54
    @80
    @0
    @54
    @53
    @80
    @0
    @54
    @53
    @80
    @0
    @54
    @53
    w3a
    cE
    c1
    @49
    cfz
    co
    wcel
    @80
    vx
    c.x
    cE
    cG
    @49
    cgrp
    cX
    c.0
    gexcl.1
    gexcl.2
    gexid.3
    gexid.4
    gexlem2
    cE
    c1
    @49
    elfzle2
    syl
    3expia
    impancom
    con3d
    ex
    ad2antrr
    mpid
    @48
    @54
    @50
    @48
    @83
    @54
    @50
    wo
    @84
    @49
    elnn0
    sylib
    ord
    3syld
    @48
    @47
    @1
    @3
    @50
    wb
    @2
    @47
    simpr
    @0
    @1
    @47
    simplr
    cE
    cN
    dvdsval3
    syl2anc
    sylibrd
    sylan2
    @0
    @16
    @18
    wo
    @1
    vx
    vy
    c.x
    cE
    cG
    @14
    cgrp
    cX
    c.0
    gexcl.1
    gexid.3
    gexid.4
    gexcl.2
    @14
    eqid
    gexlem1
    adantr
    mpjaodan
    impbid
end

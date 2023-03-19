include "cofld.mm"
include "wcel.mm"
include "cchr.mm"
include "cfv.mm"
include "cur.mm"
include "cod.mm"
include "cc0.mm"
include "eqid.mm"
include "chrval.mm"
include "cv.mm"
include "cmg.mm"
include "co.mm"
include "c0g.mm"
include "wceq.mm"
include "cn.mm"
include "crab.mm"
include "c0.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cif.mm"
include "crg.mm"
include "cbs.mm"
include "cfield.mm"
include "cdr.mm"
include "ofldfld.mm"
include "ccrg.mm"
include "isfld.mm"
include "simplbi.mm"
include "drngring.mm"
include "3syl.mm"
include "ringidcl.mm"
include "odval.mm"
include "wn.mm"
include "wral.mm"
include "wa.mm"
include "cplt.mm"
include "wbr.mm"
include "wne.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "oveq1.mm"
include "breq2d.mm"
include "imbi2d.mm"
include "ofldlt1.mm"
include "syl.mm"
include "mulg1.mm"
include "breqtrrd.mm"
include "cpo.mm"
include "w3a.mm"
include "ctos.mm"
include "ofldtos.mm"
include "tospos.mm"
include "ad2antlr.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "grpidcl.mm"
include "cmgm.mm"
include "cmnd.mm"
include "grpmnd.mm"
include "mndmgm.mm"
include "simpll.mm"
include "mulgnncl.mm"
include "syl3anc.mm"
include "peano2nnd.mm"
include "3jca.mm"
include "simpr.mm"
include "cplusg.mm"
include "cogrp.mm"
include "corng.mm"
include "simplr.mm"
include "isofld.mm"
include "simprbi.mm"
include "orngogrp.mm"
include "ogrpaddlt.mm"
include "syl131anc.mm"
include "grplid.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "mulgnnp1.mm"
include "ccmn.mm"
include "ringcmn.mm"
include "cmncom.mm"
include "eqtrd.mm"
include "3brtr4d.mm"
include "plttr.mm"
include "imp.mm"
include "syl22anc.mm"
include "exp31.mm"
include "a2d.mm"
include "nnind.mm"
include "impcom.mm"
include "cvv.mm"
include "fvex.mm"
include "ovex.mm"
include "pltne.mm"
include "mp3an23.mm"
include "adantr.mm"
include "mpd.mm"
include "necomd.mm"
include "neneqd.mm"
include "ralrimiva.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "iftrued.mm"
include "syl5eqr.mm"

theorem ofldchr
  let cF: class F
  let vm: setvar m
  let vn: setvar n
  let vy: setvar y


  assert |- ( F e. oField -> ( chr ` F ) = 0 )

  proof
    cF
    cofld
    wcel
    #
    cF
    cchr
    cfv
    #
    cF
    cur
    cfv
    #
    cF
    cod
    cfv
    #
    cfv
    #
    cc0
    @1
    cF
    @2
    @3
    @3
    eqid
    #
    @2
    eqid
    #
    @1
    eqid
    chrval
    @0
    @4
    vy
    cv
    #
    @2
    cF
    cmg
    cfv
    #
    co
    #
    cF
    c0g
    cfv
    #
    wceq
    #
    vy
    cn
    crab
    #
    c0
    wceq
    #
    cc0
    @12
    cr
    clt
    cinf
    #
    cif
    #
    cc0
    @0
    cF
    crg
    wcel
    #
    @2
    cF
    cbs
    cfv
    #
    wcel
    #
    @4
    @15
    wceq
    @0
    cF
    cfield
    wcel
    #
    cF
    cdr
    wcel
    #
    @16
    cF
    ofldfld
    @19
    @20
    cF
    ccrg
    wcel
    cF
    isfld
    simplbi
    cF
    drngring
    3syl
    #
    @17
    cF
    @2
    @17
    eqid
    #
    @6
    ringidcl
    #
    vy
    @2
    @8
    cF
    @12
    @3
    @17
    @10
    @22
    @8
    eqid
    #
    @10
    eqid
    #
    @5
    @12
    eqid
    odval
    3syl
    @0
    @13
    cc0
    @14
    @0
    @11
    wn
    #
    vy
    cn
    wral
    @13
    @0
    @26
    vy
    cn
    @0
    @7
    cn
    wcel
    #
    wa
    #
    @9
    @10
    @28
    @10
    @9
    @28
    @10
    @9
    cF
    cplt
    cfv
    #
    wbr
    #
    @10
    @9
    wne
    #
    @27
    @0
    @30
    @0
    @10
    vn
    cv
    #
    @2
    @8
    co
    #
    @29
    wbr
    #
    wi
    @0
    @10
    c1
    @2
    @8
    co
    #
    @29
    wbr
    #
    wi
    @0
    @10
    vm
    cv
    #
    @2
    @8
    co
    #
    @29
    wbr
    #
    wi
    @0
    @10
    @37
    c1
    caddc
    co
    #
    @2
    @8
    co
    #
    @29
    wbr
    #
    wi
    @0
    @30
    wi
    vn
    vm
    @7
    @32
    c1
    wceq
    #
    @34
    @36
    @0
    @43
    @33
    @35
    @10
    @29
    @32
    c1
    @2
    @8
    oveq1
    breq2d
    imbi2d
    @32
    @37
    wceq
    #
    @34
    @39
    @0
    @44
    @33
    @38
    @10
    @29
    @32
    @37
    @2
    @8
    oveq1
    breq2d
    imbi2d
    @32
    @40
    wceq
    #
    @34
    @42
    @0
    @45
    @33
    @41
    @10
    @29
    @32
    @40
    @2
    @8
    oveq1
    breq2d
    imbi2d
    @32
    @7
    wceq
    #
    @34
    @30
    @0
    @46
    @33
    @9
    @10
    @29
    @32
    @7
    @2
    @8
    oveq1
    breq2d
    imbi2d
    @0
    @10
    @2
    @35
    @29
    @29
    @2
    cF
    @10
    @25
    @6
    @29
    eqid
    #
    ofldlt1
    #
    @0
    @18
    @35
    @2
    wceq
    @0
    @16
    @18
    @21
    @23
    syl
    #
    @17
    @8
    cF
    @2
    @22
    @24
    mulg1
    syl
    breqtrrd
    @37
    cn
    wcel
    #
    @0
    @39
    @42
    @50
    @0
    @39
    @42
    @50
    @0
    wa
    #
    @39
    wa
    #
    cF
    cpo
    wcel
    #
    @10
    @17
    wcel
    #
    @38
    @17
    wcel
    #
    @41
    @17
    wcel
    #
    w3a
    #
    @39
    @38
    @41
    @29
    wbr
    #
    @42
    @0
    @53
    @50
    @39
    @0
    cF
    ctos
    wcel
    @53
    cF
    ofldtos
    cF
    tospos
    syl
    ad2antlr
    @52
    @54
    @55
    @56
    @52
    cF
    cgrp
    wcel
    #
    @54
    @0
    @59
    @50
    @39
    @0
    @16
    @59
    @21
    cF
    ringgrp
    syl
    ad2antlr
    #
    @17
    cF
    @10
    @22
    @25
    grpidcl
    syl
    #
    @52
    cF
    cmgm
    wcel
    #
    @50
    @18
    @55
    @52
    @59
    @62
    @60
    @59
    cF
    cmnd
    wcel
    @62
    cF
    grpmnd
    cF
    mndmgm
    syl
    syl
    #
    @50
    @0
    @39
    simpll
    #
    @0
    @18
    @50
    @39
    @49
    ad2antlr
    #
    @17
    @8
    cF
    @37
    @2
    @22
    @24
    mulgnncl
    syl3anc
    #
    @52
    @62
    @40
    cn
    wcel
    @18
    @56
    @63
    @52
    @37
    @64
    peano2nnd
    @65
    @17
    @8
    cF
    @40
    @2
    @22
    @24
    mulgnncl
    syl3anc
    3jca
    @51
    @39
    simpr
    @52
    @10
    @38
    cF
    cplusg
    cfv
    #
    co
    #
    @2
    @38
    @67
    co
    #
    @38
    @41
    @29
    @52
    cF
    cogrp
    wcel
    #
    @54
    @18
    @55
    @10
    @2
    @29
    wbr
    #
    @68
    @69
    @29
    wbr
    @52
    @0
    cF
    corng
    wcel
    #
    @70
    @50
    @0
    @39
    simplr
    #
    @0
    @19
    @72
    cF
    isofld
    simprbi
    cF
    orngogrp
    3syl
    @61
    @65
    @66
    @0
    @71
    @50
    @39
    @48
    ad2antlr
    @17
    @67
    @29
    cF
    @10
    @2
    @38
    @22
    @47
    @67
    eqid
    #
    ogrpaddlt
    syl131anc
    @52
    @68
    @38
    @52
    @59
    @55
    @68
    @38
    wceq
    @60
    @66
    @17
    @67
    cF
    @38
    @10
    @22
    @74
    @25
    grplid
    syl2anc
    eqcomd
    @52
    @41
    @38
    @2
    @67
    co
    #
    @69
    @52
    @50
    @18
    @41
    @75
    wceq
    @64
    @65
    @17
    @67
    @8
    cF
    @37
    @2
    @22
    @24
    @74
    mulgnnp1
    syl2anc
    @52
    cF
    ccmn
    wcel
    #
    @55
    @18
    @75
    @69
    wceq
    @52
    @0
    @16
    @76
    @73
    @21
    cF
    ringcmn
    3syl
    @66
    @65
    @17
    @67
    cF
    @38
    @2
    @22
    @74
    cmncom
    syl3anc
    eqtrd
    3brtr4d
    @53
    @57
    wa
    @39
    @58
    wa
    @42
    @17
    @29
    cF
    @10
    @38
    @41
    @22
    @47
    plttr
    imp
    syl22anc
    exp31
    a2d
    nnind
    impcom
    @0
    @30
    @31
    wi
    #
    @27
    @0
    @10
    cvv
    wcel
    @9
    cvv
    wcel
    @77
    cF
    c0g
    fvex
    @7
    @2
    @8
    ovex
    cofld
    cvv
    cvv
    @29
    cF
    @10
    @9
    @47
    pltne
    mp3an23
    adantr
    mpd
    necomd
    neneqd
    ralrimiva
    @11
    vy
    cn
    rabeq0
    sylibr
    iftrued
    eqtrd
    syl5eqr
end

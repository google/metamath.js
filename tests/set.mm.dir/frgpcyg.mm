include "c1o.mm"
include "cdom.mm"
include "wbr.mm"
include "ccyg.mm"
include "wcel.mm"
include "csdm.mm"
include "cen.mm"
include "wo.mm"
include "brdom2.mm"
include "c0.mm"
include "wceq.mm"
include "sdom1.mm"
include "cfrgp.mm"
include "cfv.mm"
include "fveq2.mm"
include "syl5eq.mm"
include "cgrp.mm"
include "cbs.mm"
include "cvv.mm"
include "0ex.mm"
include "eqid.mm"
include "frgpgrp.mm"
include "ax-mp.mm"
include "0frgp.mm"
include "0cyg.mm"
include "mp2an.mm"
include "syl6eqel.mm"
include "sylbi.mm"
include "cmg.mm"
include "cuni.mm"
include "cvrgp.mm"
include "relen.mm"
include "brrelexi.mm"
include "syl.mm"
include "wf.mm"
include "cefg.mm"
include "vrgpf.mm"
include "en1uniel.mm"
include "ffvelrnd.mm"
include "cv.mm"
include "wa.mm"
include "ccom.mm"
include "c1.mm"
include "cop.mm"
include "csn.mm"
include "zring.mm"
include "cghm.mm"
include "co.mm"
include "wrex.mm"
include "cz.mm"
include "wreu.mm"
include "zringgrp.mm"
include "uniexg.mm"
include "1zzd.mm"
include "fsnd.mm"
include "en1b.mm"
include "biimpi.mm"
include "feq2d.mm"
include "mpbird.mm"
include "zringbas.mm"
include "frgpup3.mm"
include "mp3an2i.mm"
include "adantr.mm"
include "reurex.mm"
include "wi.mm"
include "fveq1.mm"
include "fvco3.mm"
include "syl2anc.mm"
include "1z.mm"
include "fvsng.mm"
include "sylancl.mm"
include "eqeq12d.mm"
include "syl5ib.mm"
include "ad2antrr.mm"
include "ghmf.mm"
include "ad2antrl.mm"
include "ffvelrnda.mm"
include "an32s.mm"
include "cmpt.mm"
include "wral.mm"
include "cid.mm"
include "cres.mm"
include "mptresid.mm"
include "wrmo.mm"
include "syl3anc.mm"
include "reurmo.mm"
include "idghm.mm"
include "fcoi2.mm"
include "feqmptd.mm"
include "eqidd.mm"
include "oveq1.mm"
include "fmptco.mm"
include "mulgghm2.mm"
include "simprl.mm"
include "ghmco.mm"
include "eqeltrrd.mm"
include "eleq2d.mm"
include "simprr.mm"
include "oveq1d.mm"
include "mulg1.mm"
include "eqtrd.mm"
include "elsni.mm"
include "fveq2d.mm"
include "syl5ibrcom.mm"
include "sylbid.mm"
include "imp.mm"
include "mpteq2dva.mm"
include "3eqtr4d.mm"
include "coeq1.mm"
include "eqeq1d.mm"
include "rmoi.mm"
include "syl122anc.mm"
include "wb.mm"
include "mpteqb.mm"
include "id.mm"
include "mprg.mm"
include "sylib.mm"
include "r19.21bi.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "expr.mm"
include "syld.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "iscygd.mm"
include "jaoi.mm"
include "cabl.mm"
include "cygabl.mm"
include "wn.mm"
include "frgpnabl.mm"
include "con2i.mm"
include "cfn.mm"
include "c0g.mm"
include "ablgrp.mm"
include "grpidcl.mm"
include "elbasfv.mm"
include "3syl.mm"
include "com.mm"
include "1onn.mm"
include "nnfi.mm"
include "fidomtri2.mm"
include "impbii.mm"

theorem frgpcyg
  let cG: class G
  let cI: class I
  let vf: setvar f
  let vg: setvar g
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  assume frgpcyg.g: |- G = ( freeGrp ` I )


  assert |- ( I ~<_ 1o <-> G e. CycGrp )

  proof
    cI
    c1o
    cdom
    wbr
    #
    cG
    ccyg
    wcel
    #
    @0
    cI
    c1o
    csdm
    wbr
    #
    cI
    c1o
    cen
    wbr
    #
    wo
    @1
    cI
    c1o
    brdom2
    @2
    @1
    @3
    @2
    cI
    c0
    wceq
    #
    @1
    cI
    sdom1
    @4
    cG
    c0
    cfrgp
    cfv
    #
    ccyg
    @4
    cG
    cI
    cfrgp
    cfv
    @5
    frgpcyg.g
    cI
    c0
    cfrgp
    fveq2
    syl5eq
    @5
    cgrp
    wcel
    #
    @5
    cbs
    cfv
    #
    c1o
    cen
    wbr
    @5
    ccyg
    wcel
    c0
    cvv
    wcel
    @6
    0ex
    @5
    c0
    cvv
    @5
    eqid
    #
    frgpgrp
    ax-mp
    @7
    @5
    @8
    @7
    eqid
    #
    0frgp
    @7
    @5
    @9
    0cyg
    mp2an
    syl6eqel
    sylbi
    @3
    vx
    cG
    cbs
    cfv
    #
    cG
    cmg
    cfv
    #
    vn
    cG
    cI
    cuni
    #
    cI
    cvrgp
    cfv
    #
    cfv
    #
    @10
    eqid
    #
    @11
    eqid
    #
    @3
    cI
    cvv
    wcel
    #
    cG
    cgrp
    wcel
    #
    cI
    c1o
    cen
    relen
    brrelexi
    #
    cG
    cI
    cvv
    frgpcyg.g
    frgpgrp
    syl
    #
    @3
    cI
    @10
    @12
    @13
    @3
    @17
    cI
    @10
    @13
    wf
    #
    @19
    cI
    cefg
    cfv
    #
    @13
    cG
    cI
    cvv
    @10
    @22
    eqid
    @13
    eqid
    #
    frgpcyg.g
    @15
    vrgpf
    syl
    #
    cI
    en1uniel
    #
    ffvelrnd
    #
    @3
    vx
    cv
    #
    @10
    wcel
    #
    wa
    #
    vf
    cv
    #
    @13
    ccom
    #
    @12
    c1
    cop
    csn
    #
    wceq
    #
    vf
    cG
    zring
    cghm
    co
    #
    wrex
    #
    @27
    vn
    cv
    #
    @14
    @11
    co
    #
    wceq
    #
    vn
    cz
    wrex
    #
    @29
    @33
    vf
    @34
    wreu
    #
    @35
    @3
    @40
    @28
    zring
    cgrp
    wcel
    @3
    @17
    cI
    cz
    @32
    wf
    #
    @40
    zringgrp
    @19
    @3
    @41
    @12
    csn
    #
    cz
    @32
    wf
    @3
    @12
    c1
    cvv
    cz
    @3
    @17
    @12
    cvv
    wcel
    #
    @19
    cI
    cvv
    uniexg
    syl
    #
    @3
    1zzd
    fsnd
    @3
    cI
    @42
    cz
    @32
    @3
    cI
    @42
    wceq
    #
    cI
    en1b
    biimpi
    #
    feq2d
    mpbird
    cz
    @13
    vf
    @32
    cG
    zring
    cI
    cvv
    frgpcyg.g
    zringbas
    @23
    frgpup3
    mp3an2i
    adantr
    @33
    vf
    @34
    reurex
    syl
    @29
    @33
    @39
    vf
    @34
    @29
    @30
    @34
    wcel
    #
    wa
    @33
    @14
    @30
    cfv
    #
    c1
    wceq
    #
    @39
    @3
    @33
    @49
    wi
    @28
    @47
    @33
    @12
    @31
    cfv
    #
    @12
    @32
    cfv
    #
    wceq
    @3
    @49
    @12
    @31
    @32
    fveq1
    @3
    @50
    @48
    @51
    c1
    @3
    @21
    @12
    cI
    wcel
    @50
    @48
    wceq
    @24
    @25
    cI
    @10
    @12
    @30
    @13
    fvco3
    syl2anc
    @3
    @43
    c1
    cz
    wcel
    @51
    c1
    wceq
    @44
    1z
    @12
    c1
    cvv
    cz
    fvsng
    sylancl
    eqeq12d
    syl5ib
    ad2antrr
    @29
    @47
    @49
    @39
    @29
    @47
    @49
    wa
    #
    wa
    @27
    @30
    cfv
    #
    cz
    wcel
    #
    @27
    @53
    @14
    @11
    co
    #
    wceq
    #
    @39
    @3
    @52
    @28
    @54
    @3
    @52
    wa
    #
    @10
    cz
    @27
    @30
    @47
    @10
    cz
    @30
    wf
    @3
    @49
    cG
    zring
    @30
    @10
    cz
    @15
    zringbas
    ghmf
    ad2antrl
    #
    ffvelrnda
    #
    an32s
    @3
    @52
    @28
    @56
    @57
    @56
    vx
    @10
    @57
    vx
    @10
    @27
    cmpt
    #
    vx
    @10
    @55
    cmpt
    #
    wceq
    #
    @56
    vx
    @10
    wral
    #
    @57
    @60
    cid
    @10
    cres
    #
    @61
    vx
    @10
    mptresid
    @57
    vg
    cv
    #
    @13
    ccom
    #
    @13
    wceq
    #
    vg
    cG
    cG
    cghm
    co
    #
    wrmo
    #
    @64
    @68
    wcel
    #
    @64
    @13
    ccom
    #
    @13
    wceq
    #
    @61
    @68
    wcel
    @61
    @13
    ccom
    #
    @13
    wceq
    #
    @64
    @61
    wceq
    @3
    @69
    @52
    @3
    @67
    vg
    @68
    wreu
    #
    @69
    @3
    @18
    @17
    @21
    @75
    @20
    @19
    @24
    @10
    @13
    vg
    @13
    cG
    cG
    cI
    cvv
    frgpcyg.g
    @15
    @23
    frgpup3
    syl3anc
    @67
    vg
    @68
    reurmo
    syl
    adantr
    @57
    @18
    @70
    @3
    @18
    @52
    @20
    adantr
    #
    @10
    cG
    @15
    idghm
    syl
    @57
    @21
    @72
    @3
    @21
    @52
    @24
    adantr
    #
    cI
    @10
    @13
    fcoi2
    syl
    @57
    vn
    cz
    @37
    cmpt
    #
    @30
    ccom
    #
    @61
    @68
    @57
    vx
    vn
    @10
    cz
    @53
    @37
    @55
    @30
    @78
    @59
    @57
    vx
    @10
    cz
    @30
    @58
    feqmptd
    @57
    @78
    eqidd
    @36
    @53
    @14
    @11
    oveq1
    #
    fmptco
    @57
    @78
    zring
    cG
    cghm
    co
    wcel
    #
    @47
    @79
    @68
    wcel
    @57
    @18
    @14
    @10
    wcel
    #
    @81
    @76
    @3
    @82
    @52
    @26
    adantr
    #
    @10
    cG
    @11
    @14
    vn
    @78
    @16
    @78
    eqid
    @15
    mulgghm2
    syl2anc
    @3
    @47
    @49
    simprl
    cG
    zring
    cG
    @78
    @30
    ghmco
    syl2anc
    eqeltrrd
    @57
    vy
    cI
    vy
    cv
    #
    @13
    cfv
    #
    @30
    cfv
    #
    @14
    @11
    co
    #
    cmpt
    vy
    cI
    @85
    cmpt
    @73
    @13
    @57
    vy
    cI
    @87
    @85
    @57
    @84
    cI
    wcel
    #
    @87
    @85
    wceq
    #
    @57
    @88
    @84
    @42
    wcel
    #
    @89
    @57
    cI
    @42
    @84
    @3
    @45
    @52
    @46
    adantr
    eleq2d
    @57
    @89
    @90
    @48
    @14
    @11
    co
    #
    @14
    wceq
    @57
    @91
    c1
    @14
    @11
    co
    #
    @14
    @57
    @48
    c1
    @14
    @11
    @3
    @47
    @49
    simprr
    oveq1d
    @57
    @82
    @92
    @14
    wceq
    @83
    @10
    @11
    cG
    @14
    @15
    @16
    mulg1
    syl
    eqtrd
    @90
    @87
    @91
    @85
    @14
    @90
    @86
    @48
    @14
    @11
    @90
    @85
    @14
    @30
    @90
    @84
    @12
    @13
    @84
    @12
    elsni
    fveq2d
    #
    fveq2d
    oveq1d
    @93
    eqeq12d
    syl5ibrcom
    sylbid
    imp
    mpteq2dva
    @57
    vy
    vx
    cI
    @10
    @85
    @55
    @87
    @13
    @61
    @57
    cI
    @10
    @84
    @13
    @77
    ffvelrnda
    @57
    vy
    cI
    @10
    @13
    @77
    feqmptd
    #
    @57
    @61
    eqidd
    @27
    @85
    wceq
    @53
    @86
    @14
    @11
    @27
    @85
    @30
    fveq2
    oveq1d
    fmptco
    @94
    3eqtr4d
    @67
    @72
    @74
    vg
    @68
    @64
    @61
    @65
    @64
    wceq
    @66
    @71
    @13
    @65
    @64
    @13
    coeq1
    eqeq1d
    @65
    @61
    wceq
    @66
    @73
    @13
    @65
    @61
    @13
    coeq1
    eqeq1d
    rmoi
    syl122anc
    syl5eq
    @28
    @62
    @63
    wb
    vx
    @10
    vx
    @10
    @27
    @55
    @10
    mpteqb
    @28
    id
    mprg
    sylib
    r19.21bi
    an32s
    @38
    @56
    vn
    @53
    cz
    @36
    @53
    wceq
    @37
    @55
    @27
    @80
    eqeq2d
    rspcev
    syl2anc
    expr
    syld
    rexlimdva
    mpd
    iscygd
    jaoi
    sylbi
    @1
    cG
    cabl
    wcel
    #
    @0
    cG
    cygabl
    @95
    @0
    c1o
    cI
    csdm
    wbr
    #
    wn
    #
    @96
    @95
    cG
    cI
    frgpcyg.g
    frgpnabl
    con2i
    @95
    @17
    c1o
    cfn
    wcel
    #
    @0
    @97
    wb
    @95
    @18
    cG
    c0g
    cfv
    #
    @10
    wcel
    @17
    cG
    ablgrp
    @10
    cG
    @99
    @15
    @99
    eqid
    grpidcl
    @10
    cG
    cfrgp
    @99
    cI
    frgpcyg.g
    @15
    elbasfv
    3syl
    c1o
    com
    wcel
    @98
    1onn
    c1o
    nnfi
    ax-mp
    cI
    c1o
    cvv
    fidomtri2
    sylancl
    mpbird
    syl
    impbii
end

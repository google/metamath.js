include "ccnfld.mm"
include "wfun.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cc.mm"
include "cop.mm"
include "cplusg.mm"
include "caddc.mm"
include "cmulr.mm"
include "cmul.mm"
include "ctp.mm"
include "cstv.mm"
include "ccj.mm"
include "csn.mm"
include "cun.mm"
include "cts.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cmopn.mm"
include "cple.mm"
include "cle.mm"
include "cds.mm"
include "cunif.mm"
include "cmetu.mm"
include "wa.mm"
include "cdm.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wne.mm"
include "basendxnplusgndx.mm"
include "basendxnmulrndx.mm"
include "plusgndxnmulrndx.mm"
include "fvex.mm"
include "cnex.mm"
include "addex.mm"
include "mulex.mm"
include "funtp.mm"
include "mp3an.mm"
include "wf.mm"
include "cvv.mm"
include "wcel.mm"
include "cjf.mm"
include "fex.mm"
include "mp2an.mm"
include "funsn.mm"
include "pm3.2i.mm"
include "dmtpop.mm"
include "dmsnop.mm"
include "ineq12i.mm"
include "c1.mm"
include "basendx.mm"
include "c4.mm"
include "1re.mm"
include "1lt4.mm"
include "ltneii.mm"
include "starvndx.mm"
include "neeqtrri.mm"
include "eqnetri.mm"
include "c2.mm"
include "plusgndx.mm"
include "2re.mm"
include "2lt4.mm"
include "c3.mm"
include "mulrndx.mm"
include "3re.mm"
include "3lt4.mm"
include "disjtpsn.mm"
include "eqtri.mm"
include "funun.mm"
include "c9.mm"
include "tsetndx.mm"
include "cc0.mm"
include "cdc.mm"
include "9re.mm"
include "9lt10.mm"
include "plendx.mm"
include "1nn.mm"
include "2nn0.mm"
include "9nn0.mm"
include "leidi.mm"
include "decltdi.mm"
include "dsndx.mm"
include "10re.mm"
include "1nn0.mm"
include "0nn0.mm"
include "2nn.mm"
include "2pos.mm"
include "declt.mm"
include "ctsr.mm"
include "letsr.mm"
include "elexi.mm"
include "cr.mm"
include "absf.mm"
include "cxp.mm"
include "subf.mm"
include "xpex.mm"
include "coex.mm"
include "3nn0.mm"
include "unifndx.mm"
include "3nn.mm"
include "3pos.mm"
include "deccl.mm"
include "nn0rei.mm"
include "2lt3.mm"
include "dmun.mm"
include "w3a.mm"
include "1lt9.mm"
include "2lt9.mm"
include "3lt9.mm"
include "3pm3.2i.mm"
include "1lt10.mm"
include "2lt10.mm"
include "3lt10.mm"
include "ltleii.mm"
include "disjtp2.mm"
include "undisj2.mm"
include "mpbi.mm"
include "incom.mm"
include "4re.mm"
include "4lt9.mm"
include "gtneii.mm"
include "4lt10.mm"
include "4nn0.mm"
include "disjsn2.mm"
include "ax-mp.mm"
include "undisj1.mm"
include "df-cnfld.mm"
include "funeqi.mm"
include "mpbir.mm"

theorem cnfldfun



  assert |- Fun CCfld

  proof
    ccnfld
    wfun
    cnx
    cbs
    cfv
    #
    cc
    cop
    cnx
    cplusg
    cfv
    #
    caddc
    cop
    cnx
    cmulr
    cfv
    #
    cmul
    cop
    ctp
    #
    cnx
    cstv
    cfv
    #
    ccj
    cop
    csn
    #
    cun
    #
    cnx
    cts
    cfv
    #
    cabs
    cmin
    ccom
    #
    cmopn
    cfv
    #
    cop
    cnx
    cple
    cfv
    #
    cle
    cop
    cnx
    cds
    cfv
    #
    @8
    cop
    ctp
    #
    cnx
    cunif
    cfv
    #
    @8
    cmetu
    cfv
    #
    cop
    csn
    #
    cun
    #
    cun
    #
    wfun
    #
    @6
    wfun
    #
    @16
    wfun
    #
    wa
    @6
    cdm
    #
    @16
    cdm
    #
    cin
    #
    c0
    wceq
    @18
    @19
    @20
    @3
    wfun
    #
    @5
    wfun
    #
    wa
    @3
    cdm
    #
    @5
    cdm
    #
    cin
    #
    c0
    wceq
    @19
    @24
    @25
    @0
    @1
    wne
    @0
    @2
    wne
    @1
    @2
    wne
    @24
    basendxnplusgndx
    basendxnmulrndx
    plusgndxnmulrndx
    @0
    @1
    @2
    cc
    caddc
    cmul
    cnx
    cbs
    fvex
    cnx
    cplusg
    fvex
    cnx
    cmulr
    fvex
    cnex
    addex
    mulex
    funtp
    mp3an
    @4
    ccj
    cnx
    cstv
    fvex
    cc
    cc
    ccj
    wf
    cc
    cvv
    wcel
    #
    ccj
    cvv
    wcel
    cjf
    cnex
    cc
    cc
    cvv
    ccj
    fex
    mp2an
    #
    funsn
    pm3.2i
    @28
    @0
    @1
    @2
    ctp
    #
    @4
    csn
    #
    cin
    #
    c0
    @26
    @31
    @27
    @32
    @0
    cc
    @1
    caddc
    @2
    cmul
    cnex
    addex
    mulex
    dmtpop
    #
    @4
    ccj
    @30
    dmsnop
    #
    ineq12i
    @0
    @4
    wne
    @1
    @4
    wne
    @2
    @4
    wne
    @33
    c0
    wceq
    @0
    c1
    @4
    basendx
    c1
    c4
    @4
    c1
    c4
    1re
    1lt4
    ltneii
    starvndx
    neeqtrri
    eqnetri
    @1
    c2
    @4
    plusgndx
    c2
    c4
    @4
    c2
    c4
    2re
    2lt4
    ltneii
    starvndx
    neeqtrri
    eqnetri
    @2
    c3
    @4
    mulrndx
    c3
    c4
    @4
    c3
    c4
    3re
    3lt4
    ltneii
    starvndx
    neeqtrri
    eqnetri
    @0
    @1
    @2
    @4
    disjtpsn
    mp3an
    eqtri
    @3
    @5
    funun
    mp2an
    @12
    wfun
    #
    @15
    wfun
    #
    wa
    @12
    cdm
    #
    @15
    cdm
    #
    cin
    #
    c0
    wceq
    @20
    @36
    @37
    @7
    @10
    wne
    @7
    @11
    wne
    @10
    @11
    wne
    @36
    @7
    c9
    @10
    tsetndx
    c9
    c1
    cc0
    cdc
    #
    @10
    c9
    @41
    9re
    9lt10
    ltneii
    plendx
    neeqtrri
    eqnetri
    @7
    c9
    @11
    tsetndx
    c9
    c1
    c2
    cdc
    #
    @11
    c9
    @42
    9re
    c1
    c2
    c9
    1nn
    2nn0
    9nn0
    c9
    9re
    leidi
    #
    decltdi
    ltneii
    dsndx
    neeqtrri
    eqnetri
    @10
    @41
    @11
    plendx
    @41
    @42
    @11
    @41
    @42
    10re
    c1
    cc0
    c2
    1nn0
    0nn0
    2nn
    2pos
    declt
    ltneii
    dsndx
    neeqtrri
    eqnetri
    @7
    @10
    @11
    @9
    cle
    @8
    cnx
    cts
    fvex
    cnx
    cple
    fvex
    cnx
    cds
    fvex
    @8
    cmopn
    fvex
    #
    cle
    ctsr
    letsr
    elexi
    #
    cabs
    cmin
    cc
    cr
    cabs
    wf
    @29
    cabs
    cvv
    wcel
    absf
    cnex
    cc
    cr
    cvv
    cabs
    fex
    mp2an
    cc
    cc
    cxp
    #
    cc
    cmin
    wf
    @46
    cvv
    wcel
    cmin
    cvv
    wcel
    subf
    cc
    cc
    cnex
    cnex
    xpex
    @46
    cc
    cvv
    cmin
    fex
    mp2an
    coex
    #
    funtp
    mp3an
    @13
    @14
    cnx
    cunif
    fvex
    @8
    cmetu
    fvex
    #
    funsn
    pm3.2i
    @40
    @7
    @10
    @11
    ctp
    #
    @13
    csn
    #
    cin
    #
    c0
    @38
    @49
    @39
    @50
    @7
    @9
    @10
    cle
    @11
    @8
    @44
    @45
    @47
    dmtpop
    #
    @13
    @14
    @48
    dmsnop
    #
    ineq12i
    @7
    @13
    wne
    @10
    @13
    wne
    @11
    @13
    wne
    @51
    c0
    wceq
    @7
    c9
    @13
    tsetndx
    c9
    c1
    c3
    cdc
    #
    @13
    c9
    @54
    9re
    c1
    c3
    c9
    1nn
    3nn0
    9nn0
    @43
    decltdi
    ltneii
    unifndx
    neeqtrri
    eqnetri
    @10
    @41
    @13
    plendx
    @41
    @54
    @13
    @41
    @54
    10re
    c1
    cc0
    c3
    1nn0
    0nn0
    3nn
    3pos
    declt
    ltneii
    unifndx
    neeqtrri
    eqnetri
    @11
    @42
    @13
    dsndx
    @42
    @54
    @13
    @42
    @54
    @42
    c1
    c2
    1nn0
    2nn0
    deccl
    nn0rei
    c1
    c2
    c3
    1nn0
    2nn0
    3nn
    2lt3
    declt
    ltneii
    unifndx
    neeqtrri
    eqnetri
    @7
    @10
    @11
    @13
    disjtpsn
    mp3an
    eqtri
    @12
    @15
    funun
    mp2an
    pm3.2i
    @23
    @26
    @27
    cun
    #
    @38
    @39
    cun
    #
    cin
    #
    c0
    @21
    @55
    @22
    @56
    @3
    @5
    dmun
    @12
    @15
    dmun
    ineq12i
    @26
    @56
    cin
    c0
    wceq
    #
    @27
    @56
    cin
    c0
    wceq
    #
    wa
    @57
    c0
    wceq
    @58
    @59
    @26
    @38
    cin
    #
    c0
    wceq
    #
    @26
    @39
    cin
    #
    c0
    wceq
    #
    wa
    @58
    @61
    @63
    @60
    @31
    @49
    cin
    #
    c0
    @26
    @31
    @38
    @49
    @34
    @52
    ineq12i
    @0
    @7
    wne
    #
    @1
    @7
    wne
    #
    @2
    @7
    wne
    #
    w3a
    @0
    @10
    wne
    #
    @1
    @10
    wne
    #
    @2
    @10
    wne
    #
    w3a
    @0
    @11
    wne
    #
    @1
    @11
    wne
    #
    @2
    @11
    wne
    #
    w3a
    @64
    c0
    wceq
    @65
    @66
    @67
    @0
    c1
    @7
    basendx
    c1
    c9
    @7
    c1
    c9
    1re
    1lt9
    ltneii
    tsetndx
    neeqtrri
    eqnetri
    @1
    c2
    @7
    plusgndx
    c2
    c9
    @7
    c2
    c9
    2re
    2lt9
    ltneii
    tsetndx
    neeqtrri
    eqnetri
    @2
    c3
    @7
    mulrndx
    c3
    c9
    @7
    c3
    c9
    3re
    3lt9
    ltneii
    tsetndx
    neeqtrri
    eqnetri
    3pm3.2i
    @68
    @69
    @70
    @0
    c1
    @10
    basendx
    c1
    @41
    @10
    c1
    @41
    1re
    1lt10
    ltneii
    plendx
    neeqtrri
    eqnetri
    @1
    c2
    @10
    plusgndx
    c2
    @41
    @10
    c2
    @41
    2re
    2lt10
    ltneii
    plendx
    neeqtrri
    eqnetri
    @2
    c3
    @10
    mulrndx
    c3
    @41
    @10
    c3
    @41
    3re
    3lt10
    ltneii
    plendx
    neeqtrri
    eqnetri
    3pm3.2i
    @71
    @72
    @73
    @0
    c1
    @11
    basendx
    c1
    @42
    @11
    c1
    @42
    1re
    c1
    c2
    c1
    1nn
    2nn0
    1nn0
    c1
    c9
    1re
    9re
    1lt9
    ltleii
    #
    decltdi
    ltneii
    dsndx
    neeqtrri
    eqnetri
    @1
    c2
    @11
    plusgndx
    c2
    @42
    @11
    c2
    @42
    2re
    c1
    c2
    c2
    1nn
    2nn0
    2nn0
    c2
    c9
    2re
    9re
    2lt9
    ltleii
    #
    decltdi
    ltneii
    dsndx
    neeqtrri
    eqnetri
    @2
    c3
    @11
    mulrndx
    c3
    @42
    @11
    c3
    @42
    3re
    c1
    c2
    c3
    1nn
    2nn0
    3nn0
    c3
    c9
    3re
    9re
    3lt9
    ltleii
    #
    decltdi
    ltneii
    dsndx
    neeqtrri
    eqnetri
    3pm3.2i
    @0
    @1
    @2
    @7
    @10
    @11
    disjtp2
    mp3an
    eqtri
    @62
    @31
    @50
    cin
    #
    c0
    @26
    @31
    @39
    @50
    @34
    @53
    ineq12i
    @0
    @13
    wne
    @1
    @13
    wne
    @2
    @13
    wne
    @77
    c0
    wceq
    @0
    c1
    @13
    basendx
    c1
    @54
    @13
    c1
    @54
    1re
    c1
    c3
    c1
    1nn
    3nn0
    1nn0
    @74
    decltdi
    ltneii
    unifndx
    neeqtrri
    eqnetri
    @1
    c2
    @13
    plusgndx
    c2
    @54
    @13
    c2
    @54
    2re
    c1
    c3
    c2
    1nn
    3nn0
    2nn0
    @75
    decltdi
    ltneii
    unifndx
    neeqtrri
    eqnetri
    @2
    c3
    @13
    mulrndx
    c3
    @54
    @13
    c3
    @54
    3re
    c1
    c3
    c3
    1nn
    3nn0
    3nn0
    @76
    decltdi
    ltneii
    unifndx
    neeqtrri
    eqnetri
    @0
    @1
    @2
    @13
    disjtpsn
    mp3an
    eqtri
    pm3.2i
    @26
    @38
    @39
    undisj2
    mpbi
    @27
    @38
    cin
    #
    c0
    wceq
    #
    @27
    @39
    cin
    #
    c0
    wceq
    #
    wa
    @59
    @79
    @81
    @78
    @32
    @49
    cin
    #
    c0
    @27
    @32
    @38
    @49
    @35
    @52
    ineq12i
    @82
    @49
    @32
    cin
    #
    c0
    @32
    @49
    incom
    @7
    @4
    wne
    @10
    @4
    wne
    @11
    @4
    wne
    @83
    c0
    wceq
    @7
    c9
    @4
    tsetndx
    c9
    c4
    @4
    c4
    c9
    4re
    4lt9
    gtneii
    starvndx
    neeqtrri
    eqnetri
    @10
    @41
    @4
    plendx
    @41
    c4
    @4
    c4
    @41
    4re
    4lt10
    gtneii
    starvndx
    neeqtrri
    eqnetri
    @11
    @42
    @4
    dsndx
    @42
    c4
    @4
    c4
    @42
    4re
    c1
    c2
    c4
    1nn
    2nn0
    4nn0
    c4
    c9
    4re
    9re
    4lt9
    ltleii
    #
    decltdi
    gtneii
    starvndx
    neeqtrri
    eqnetri
    @7
    @10
    @11
    @4
    disjtpsn
    mp3an
    eqtri
    eqtri
    @80
    @32
    @50
    cin
    #
    c0
    @27
    @32
    @39
    @50
    @35
    @53
    ineq12i
    @4
    @13
    wne
    @85
    c0
    wceq
    @4
    c4
    @13
    starvndx
    c4
    @54
    @13
    c4
    @54
    4re
    c1
    c3
    c4
    1nn
    3nn0
    4nn0
    @84
    decltdi
    ltneii
    unifndx
    neeqtrri
    eqnetri
    @4
    @13
    disjsn2
    ax-mp
    eqtri
    pm3.2i
    @27
    @38
    @39
    undisj2
    mpbi
    pm3.2i
    @26
    @27
    @56
    undisj1
    mpbi
    eqtri
    @6
    @16
    funun
    mp2an
    ccnfld
    @17
    df-cnfld
    funeqi
    mpbir
end

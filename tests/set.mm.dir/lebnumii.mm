include "cii.mm"
include "wss.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cuni.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cxp.mm"
include "cres.mm"
include "cbl.mm"
include "cfv.mm"
include "wrex.mm"
include "wral.mm"
include "crp.mm"
include "cdiv.mm"
include "cfz.mm"
include "cn.mm"
include "df-ii.mm"
include "cme.mm"
include "wcel.mm"
include "cc.mm"
include "cnmet.mm"
include "cr.mm"
include "unitssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "metres2.mm"
include "mp2an.mm"
include "a1i.mm"
include "ccmp.mm"
include "iicmp.mm"
include "simpl.mm"
include "simpr.mm"
include "lebnum.mm"
include "cfl.mm"
include "caddc.mm"
include "cn0.mm"
include "cle.mm"
include "wbr.mm"
include "rpreccl.mm"
include "adantl.mm"
include "rpred.mm"
include "rpge0d.mm"
include "flge0nn0.mm"
include "syl2anc.mm"
include "nn0p1nn.mm"
include "syl.mm"
include "wi.mm"
include "elfznn.mm"
include "nnrpd.mm"
include "adantr.mm"
include "rpdivcld.mm"
include "cmul.mm"
include "elfzle2.mm"
include "nnred.mm"
include "recnd.mm"
include "mulid1d.mm"
include "breqtrrd.mm"
include "clt.mm"
include "wb.mm"
include "1re.mm"
include "nngt0d.mm"
include "ledivmul.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "0re.mm"
include "elicc2i.mm"
include "syl3anbrc.mm"
include "oveq1.mm"
include "sseq1d.mm"
include "rexbidv.mm"
include "rspcv.mm"
include "cioo.mm"
include "cin.mm"
include "cxr.mm"
include "simplr.mm"
include "resubcld.mm"
include "rexrd.mm"
include "readdcld.mm"
include "nnm1nn0.mm"
include "nn0red.mm"
include "nndivred.mm"
include "nnne0d.mm"
include "divsubdird.mm"
include "ax-1cn.mm"
include "nncan.mm"
include "sylancl.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "rprecred.mm"
include "flltp1.mm"
include "rpgt0.mm"
include "ad2antlr.mm"
include "ltdiv23.mm"
include "syl122anc.mm"
include "mpbid.mm"
include "eqbrtrd.mm"
include "ltsub23d.mm"
include "ltaddrpd.mm"
include "iccssioo.mm"
include "syl22anc.mm"
include "0red.mm"
include "nn0ge0d.mm"
include "divge0.mm"
include "iccss.mm"
include "ssind.mm"
include "cxmt.mm"
include "eqid.mm"
include "rexmet.mm"
include "sseqin2.mm"
include "mpbi.mm"
include "syl6eleqr.mm"
include "rpxr.mm"
include "xpss12.mm"
include "resabs1.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "blres.mm"
include "syl3anc.mm"
include "bl2ioo.mm"
include "ineq1d.mm"
include "eqtrd.mm"
include "sseqtr4d.mm"
include "sstr2.mm"
include "reximdv.mm"
include "syld.mm"
include "ralrimdva.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "raleqbidv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem lebnumii
  let vu: setvar u
  let cU: class U
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x

  disjoint k n
  disjoint k u
  disjoint U k
  disjoint n u
  disjoint U n
  disjoint U u
  disjoint k r
  disjoint k x
  disjoint n r
  disjoint n x
  disjoint r u
  disjoint r x
  disjoint U r
  disjoint u x
  disjoint U x
  assert |- ( ( U C_ II /\ ( 0 [,] 1 ) = U. U ) -> E. n e. NN A. k e. ( 1 ... n ) E. u e. U ( ( ( k - 1 ) / n ) [,] ( k / n ) ) C_ u )

  proof
    cU
    cii
    wss
    #
    cc0
    c1
    cicc
    co
    #
    cU
    cuni
    wceq
    #
    wa
    #
    vx
    cv
    #
    vr
    cv
    #
    cabs
    cmin
    ccom
    #
    @1
    @1
    cxp
    #
    cres
    #
    cbl
    cfv
    #
    co
    #
    vu
    cv
    #
    wss
    #
    vu
    cU
    wrex
    #
    vx
    @1
    wral
    #
    vr
    crp
    wrex
    vk
    cv
    #
    c1
    cmin
    co
    #
    vn
    cv
    #
    cdiv
    co
    #
    @15
    @17
    cdiv
    co
    #
    cicc
    co
    #
    @11
    wss
    #
    vu
    cU
    wrex
    #
    vk
    c1
    @17
    cfz
    co
    #
    wral
    #
    vn
    cn
    wrex
    #
    @3
    vx
    vu
    @8
    cU
    cii
    @1
    vr
    df-ii
    @8
    @1
    cme
    cfv
    wcel
    #
    @3
    @6
    cc
    cme
    cfv
    wcel
    @1
    cc
    wss
    @26
    cnmet
    @1
    cr
    cc
    unitssre
    ax-resscn
    sstri
    @6
    @1
    cc
    metres2
    mp2an
    a1i
    cii
    ccmp
    wcel
    @3
    iicmp
    a1i
    @0
    @2
    simpl
    @0
    @2
    simpr
    lebnum
    @3
    @14
    @25
    vr
    crp
    @3
    @5
    crp
    wcel
    #
    wa
    #
    c1
    @5
    cdiv
    co
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cn
    wcel
    #
    @14
    @16
    @31
    cdiv
    co
    #
    @15
    @31
    cdiv
    co
    #
    cicc
    co
    #
    @11
    wss
    #
    vu
    cU
    wrex
    #
    vk
    c1
    @31
    cfz
    co
    #
    wral
    #
    @25
    @28
    @30
    cn0
    wcel
    #
    @32
    @28
    @29
    cr
    wcel
    #
    cc0
    @29
    cle
    wbr
    @40
    @28
    @29
    @27
    @29
    crp
    wcel
    @3
    @5
    rpreccl
    adantl
    #
    rpred
    @28
    @29
    @42
    rpge0d
    @29
    flge0nn0
    syl2anc
    @30
    nn0p1nn
    syl
    #
    @28
    @14
    @37
    vk
    @38
    @28
    @15
    @38
    wcel
    #
    wa
    #
    @14
    @34
    @5
    @9
    co
    #
    @11
    wss
    #
    vu
    cU
    wrex
    #
    @37
    @45
    @34
    @1
    wcel
    #
    @14
    @48
    wi
    @45
    @34
    cr
    wcel
    #
    cc0
    @34
    cle
    wbr
    @34
    c1
    cle
    wbr
    #
    @49
    @45
    @34
    @45
    @15
    @31
    @45
    @15
    @44
    @15
    cn
    wcel
    #
    @28
    @15
    @31
    elfznn
    adantl
    #
    nnrpd
    @45
    @31
    @28
    @32
    @44
    @43
    adantr
    #
    nnrpd
    rpdivcld
    #
    rpred
    #
    @45
    @34
    @55
    rpge0d
    @45
    @51
    @15
    @31
    c1
    cmul
    co
    #
    cle
    wbr
    #
    @45
    @15
    @31
    @57
    cle
    @44
    @15
    @31
    cle
    wbr
    @28
    @15
    c1
    @31
    elfzle2
    adantl
    @45
    @31
    @45
    @31
    @45
    @31
    @54
    nnred
    #
    recnd
    #
    mulid1d
    breqtrrd
    @45
    @15
    cr
    wcel
    c1
    cr
    wcel
    #
    @31
    cr
    wcel
    #
    cc0
    @31
    clt
    wbr
    #
    @51
    @58
    wb
    @45
    @15
    @53
    nnred
    #
    @61
    @45
    1re
    a1i
    #
    @59
    @45
    @31
    @54
    nngt0d
    #
    @15
    c1
    @31
    ledivmul
    syl112anc
    mpbird
    #
    cc0
    c1
    @34
    0re
    1re
    elicc2i
    syl3anbrc
    #
    @13
    @48
    vx
    @34
    @1
    @4
    @34
    wceq
    #
    @12
    @47
    vu
    cU
    @69
    @10
    @46
    @11
    @4
    @34
    @5
    @9
    oveq1
    sseq1d
    rexbidv
    rspcv
    syl
    @45
    @47
    @36
    vu
    cU
    @45
    @35
    @46
    wss
    @47
    @36
    wi
    @45
    @35
    @34
    @5
    cmin
    co
    #
    @34
    @5
    caddc
    co
    #
    cioo
    co
    #
    @1
    cin
    #
    @46
    @45
    @35
    @72
    @1
    @45
    @70
    cxr
    wcel
    @71
    cxr
    wcel
    @70
    @33
    clt
    wbr
    @34
    @71
    clt
    wbr
    @35
    @72
    wss
    @45
    @70
    @45
    @34
    @5
    @56
    @45
    @5
    @3
    @27
    @44
    simplr
    #
    rpred
    #
    resubcld
    rexrd
    @45
    @71
    @45
    @34
    @5
    @56
    @75
    readdcld
    rexrd
    @45
    @34
    @33
    @5
    @56
    @45
    @16
    @31
    @45
    @16
    @45
    @52
    @16
    cn0
    wcel
    @53
    @15
    nnm1nn0
    syl
    #
    nn0red
    #
    @54
    nndivred
    @75
    @45
    @34
    @33
    cmin
    co
    #
    c1
    @31
    cdiv
    co
    #
    @5
    clt
    @45
    @15
    @16
    cmin
    co
    #
    @31
    cdiv
    co
    @78
    @79
    @45
    @15
    @16
    @31
    @45
    @15
    @64
    recnd
    #
    @45
    @16
    @77
    recnd
    @60
    @45
    @31
    @54
    nnne0d
    divsubdird
    @45
    @80
    c1
    @31
    cdiv
    @45
    @15
    cc
    wcel
    c1
    cc
    wcel
    @80
    c1
    wceq
    @81
    ax-1cn
    @15
    c1
    nncan
    sylancl
    oveq1d
    eqtr3d
    @45
    @29
    @31
    clt
    wbr
    #
    @79
    @5
    clt
    wbr
    #
    @45
    @41
    @82
    @45
    @5
    @74
    rprecred
    @29
    flltp1
    syl
    @45
    @61
    @5
    cr
    wcel
    #
    cc0
    @5
    clt
    wbr
    #
    @62
    @63
    @82
    @83
    wb
    @65
    @75
    @27
    @85
    @3
    @44
    @5
    rpgt0
    ad2antlr
    @59
    @66
    c1
    @5
    @31
    ltdiv23
    syl122anc
    mpbid
    eqbrtrd
    ltsub23d
    @45
    @34
    @5
    @56
    @74
    ltaddrpd
    @70
    @71
    @33
    @34
    iccssioo
    syl22anc
    @45
    cc0
    cr
    wcel
    @61
    cc0
    @33
    cle
    wbr
    #
    @51
    @35
    @1
    wss
    @45
    0red
    @65
    @45
    @16
    cr
    wcel
    cc0
    @16
    cle
    wbr
    @62
    @63
    @86
    @77
    @45
    @16
    @76
    nn0ge0d
    @59
    @66
    @16
    @31
    divge0
    syl22anc
    @67
    cc0
    c1
    @33
    @34
    iccss
    syl22anc
    ssind
    @45
    @46
    @34
    @5
    @6
    cr
    cr
    cxp
    #
    cres
    #
    cbl
    cfv
    co
    #
    @1
    cin
    #
    @73
    @45
    @88
    cr
    cxmt
    cfv
    wcel
    #
    @34
    cr
    @1
    cin
    #
    wcel
    @5
    cxr
    wcel
    #
    @46
    @90
    wceq
    @91
    @45
    @88
    @88
    eqid
    #
    rexmet
    a1i
    @45
    @34
    @1
    @92
    @68
    @1
    cr
    wss
    #
    @92
    @1
    wceq
    unitssre
    @1
    cr
    sseqin2
    mpbi
    syl6eleqr
    @27
    @93
    @3
    @44
    @5
    rpxr
    ad2antlr
    @8
    @88
    @34
    @5
    cr
    @1
    @88
    @7
    cres
    #
    @8
    @7
    @87
    wss
    #
    @96
    @8
    wceq
    @95
    @95
    @97
    unitssre
    unitssre
    @1
    cr
    @1
    cr
    xpss12
    mp2an
    @6
    @7
    @87
    resabs1
    ax-mp
    eqcomi
    blres
    syl3anc
    @45
    @89
    @72
    @1
    @45
    @50
    @84
    @89
    @72
    wceq
    @56
    @75
    @34
    @5
    @88
    @94
    bl2ioo
    syl2anc
    ineq1d
    eqtrd
    sseqtr4d
    @35
    @46
    @11
    sstr2
    syl
    reximdv
    syld
    ralrimdva
    @24
    @39
    vn
    @31
    cn
    @17
    @31
    wceq
    #
    @22
    @37
    vk
    @23
    @38
    @17
    @31
    c1
    cfz
    oveq2
    @98
    @21
    @36
    vu
    cU
    @98
    @20
    @35
    @11
    @98
    @18
    @33
    @19
    @34
    cicc
    @17
    @31
    @16
    cdiv
    oveq2
    @17
    @31
    @15
    cdiv
    oveq2
    oveq12d
    sseq1d
    rexbidv
    raleqbidv
    rspcev
    syl6an
    rexlimdva
    mpd
end

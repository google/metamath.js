include "cv.mm"
include "cun.mm"
include "cfv.mm"
include "wss.mm"
include "cpw.mm"
include "wral.mm"
include "wceq.mm"
include "wi.mm"
include "wn.mm"
include "wa.mm"
include "cmap.mm"
include "co.mm"
include "wrex.mm"
include "wal.mm"
include "cvv.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wex.mm"
include "wne.mm"
include "c1o.mm"
include "wcel.mm"
include "con0.mm"
include "1on.mm"
include "elexi.mm"
include "1n0.mm"
include "nelsn.mm"
include "ax-mp.mm"
include "eldif.mm"
include "ne0i.mm"
include "sylbir.mm"
include "mp2an.mm"
include "r19.2zb.mm"
include "mpbi.mm"
include "rexex.mm"
include "rexanali.mm"
include "exbii.mm"
include "exnal.mm"
include "sylbb.mm"
include "3syl.mm"
include "cin.mm"
include "cmpt.mm"
include "wf.mm"
include "id.mm"
include "difssd.mm"
include "sselpwd.mm"
include "adantr.mm"
include "eqid.mm"
include "fmptd.mm"
include "pwexg.mm"
include "elmapd.mm"
include "mpbird.mm"
include "simpllr.mm"
include "difeq2.mm"
include "cbvmptv.mm"
include "syl6eq.mm"
include "adantl.mm"
include "simplll.mm"
include "simplr.mm"
include "elpwid.mm"
include "simpr.mm"
include "unssd.mm"
include "vex.mm"
include "difexi.mm"
include "a1i.mm"
include "fvmptd.mm"
include "weq.mm"
include "uneq12d.mm"
include "difindi.mm"
include "syl6eqr.mm"
include "sseq12d.mm"
include "ralbidva.mm"
include "eqeq1d.mm"
include "imbi2d.mm"
include "notbid.mm"
include "anbi12d.mm"
include "pwidg.mm"
include "ssid.mm"
include "eldifsni.mm"
include "neneqd.mm"
include "uneq1.mm"
include "ssequn2.mm"
include "syl6bbr.mm"
include "ineq1.mm"
include "difeq2d.mm"
include "sseq1.mm"
include "ineq2.mm"
include "inidm.mm"
include "difid.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "rspc2ev.mm"
include "syl112anc.mm"
include "rexbii.mm"
include "rexnal.mm"
include "syl.mm"
include "inss1.mm"
include "ssun1.mm"
include "sstri.mm"
include "sscon.mm"
include "rgen2w.mm"
include "jctil.mm"
include "rspcedvd.mm"
include "mprg.mm"

theorem clsk3nimkb
  let vt: setvar t
  let vk: setvar k
  let vs: setvar s
  let vb: setvar b
  let vx: setvar x
  let vz: setvar z

  disjoint b k
  disjoint b t
  disjoint b s
  disjoint k t
  disjoint k s
  disjoint s t
  disjoint b x
  disjoint b z
  disjoint k x
  disjoint k z
  disjoint t x
  disjoint t z
  disjoint s x
  disjoint s z
  disjoint x z
  assert |- -. A. b A. k e. ( ~P b ^m ~P b ) ( A. s e. ~P b A. t e. ~P b ( k ` ( s u. t ) ) C_ ( ( k ` s ) u. ( k ` t ) ) -> A. s e. ~P b A. t e. ~P b ( ( s u. t ) = b -> ( ( k ` s ) u. ( k ` t ) ) = b ) )

  proof
    vs
    cv
    #
    vt
    cv
    #
    cun
    #
    vk
    cv
    #
    cfv
    #
    @0
    @3
    cfv
    #
    @1
    @3
    cfv
    #
    cun
    #
    wss
    #
    vt
    vb
    cv
    #
    cpw
    #
    wral
    #
    vs
    @10
    wral
    #
    @2
    @9
    wceq
    #
    @7
    @9
    wceq
    #
    wi
    #
    vt
    @10
    wral
    #
    vs
    @10
    wral
    #
    wn
    #
    wa
    #
    vk
    @10
    @10
    cmap
    co
    #
    wrex
    #
    @12
    @17
    wi
    vk
    @20
    wral
    #
    vb
    wal
    wn
    #
    vb
    cvv
    c0
    csn
    #
    cdif
    #
    @21
    vb
    @25
    wral
    #
    @21
    vb
    @25
    wrex
    #
    @21
    vb
    wex
    #
    @23
    @25
    c0
    wne
    #
    @26
    @27
    wi
    c1o
    cvv
    wcel
    #
    c1o
    @24
    wcel
    wn
    #
    @29
    c1o
    con0
    1on
    elexi
    c1o
    c0
    wne
    @31
    1n0
    c1o
    c0
    nelsn
    ax-mp
    @30
    @31
    wa
    c1o
    @25
    wcel
    @29
    c1o
    cvv
    @24
    eldif
    @25
    c1o
    ne0i
    sylbir
    mp2an
    @21
    vb
    @25
    r19.2zb
    mpbi
    @21
    vb
    @25
    rexex
    @28
    @22
    wn
    #
    vb
    wex
    @23
    @21
    @32
    vb
    @12
    @17
    vk
    @20
    rexanali
    exbii
    @22
    vb
    exnal
    sylbb
    3syl
    @9
    @25
    wcel
    #
    @19
    @9
    @2
    cdif
    #
    @9
    @0
    @1
    cin
    #
    cdif
    #
    wss
    #
    vt
    @10
    wral
    #
    vs
    @10
    wral
    #
    @13
    @36
    @9
    wceq
    #
    wi
    #
    vt
    @10
    wral
    #
    vs
    @10
    wral
    #
    wn
    #
    wa
    vk
    vx
    @10
    @9
    vx
    cv
    #
    cdif
    #
    cmpt
    #
    @20
    @33
    @47
    @20
    wcel
    @10
    @10
    @47
    wf
    @33
    vx
    @10
    @46
    @10
    @47
    @33
    @46
    @10
    wcel
    @45
    @10
    wcel
    @33
    @46
    @9
    @25
    @33
    id
    @33
    @9
    @45
    difssd
    sselpwd
    adantr
    @47
    eqid
    fmptd
    @33
    @10
    @10
    @47
    cvv
    cvv
    @9
    @25
    pwexg
    #
    @48
    elmapd
    mpbird
    @33
    @3
    @47
    wceq
    #
    wa
    #
    @12
    @39
    @18
    @44
    @50
    @11
    @38
    vs
    @10
    @50
    @0
    @10
    wcel
    #
    wa
    #
    @8
    @37
    vt
    @10
    @52
    @1
    @10
    wcel
    #
    wa
    #
    @4
    @34
    @7
    @36
    @54
    vz
    @2
    @9
    vz
    cv
    #
    cdif
    #
    @34
    @10
    @3
    cvv
    @54
    @3
    @47
    vz
    @10
    @56
    cmpt
    @33
    @49
    @51
    @53
    simpllr
    vx
    vz
    @10
    @46
    @56
    @45
    @55
    @9
    difeq2
    cbvmptv
    syl6eq
    #
    @55
    @2
    wceq
    @56
    @34
    wceq
    @54
    @55
    @2
    @9
    difeq2
    adantl
    @54
    @2
    @9
    @25
    @33
    @49
    @51
    @53
    simplll
    @54
    @0
    @1
    @9
    @54
    @0
    @9
    @50
    @51
    @53
    simplr
    #
    elpwid
    @54
    @1
    @9
    @52
    @53
    simpr
    #
    elpwid
    unssd
    sselpwd
    @34
    cvv
    wcel
    @54
    @9
    @2
    vb
    vex
    #
    difexi
    a1i
    fvmptd
    @54
    @7
    @9
    @0
    cdif
    #
    @9
    @1
    cdif
    #
    cun
    @36
    @54
    @5
    @61
    @6
    @62
    @54
    vz
    @0
    @56
    @61
    @10
    @3
    cvv
    @57
    vz
    vs
    weq
    @56
    @61
    wceq
    @54
    @55
    @0
    @9
    difeq2
    adantl
    @58
    @61
    cvv
    wcel
    @54
    @9
    @0
    @60
    difexi
    a1i
    fvmptd
    @54
    vz
    @1
    @56
    @62
    @10
    @3
    cvv
    @57
    vz
    vt
    weq
    @56
    @62
    wceq
    @54
    @55
    @1
    @9
    difeq2
    adantl
    @59
    @62
    cvv
    wcel
    @54
    @9
    @1
    @60
    difexi
    a1i
    fvmptd
    uneq12d
    @9
    @0
    @1
    difindi
    syl6eqr
    #
    sseq12d
    ralbidva
    ralbidva
    @50
    @17
    @43
    @50
    @16
    @42
    vs
    @10
    @52
    @15
    @41
    vt
    @10
    @54
    @14
    @40
    @13
    @54
    @7
    @36
    @9
    @63
    eqeq1d
    imbi2d
    ralbidva
    ralbidva
    notbid
    anbi12d
    @33
    @44
    @39
    @33
    @13
    @40
    wn
    #
    wa
    #
    vt
    @10
    wrex
    #
    vs
    @10
    wrex
    #
    @44
    @33
    @9
    @10
    wcel
    #
    @68
    @9
    @9
    wss
    #
    @9
    c0
    wceq
    #
    wn
    #
    @67
    @9
    @25
    pwidg
    #
    @72
    @69
    @33
    @9
    ssid
    a1i
    @33
    @9
    c0
    @9
    cvv
    c0
    eldifsni
    neneqd
    @65
    @69
    @71
    wa
    @1
    @9
    wss
    #
    @9
    @9
    @1
    cin
    #
    cdif
    #
    @9
    wceq
    #
    wn
    #
    wa
    vs
    vt
    @9
    @9
    @10
    @10
    vs
    vb
    weq
    #
    @13
    @73
    @64
    @77
    @78
    @13
    @9
    @1
    cun
    #
    @9
    wceq
    @73
    @78
    @2
    @79
    @9
    @0
    @9
    @1
    uneq1
    eqeq1d
    @1
    @9
    ssequn2
    syl6bbr
    @78
    @40
    @76
    @78
    @36
    @75
    @9
    @78
    @35
    @74
    @9
    @0
    @9
    @1
    ineq1
    difeq2d
    eqeq1d
    notbid
    anbi12d
    vt
    vb
    weq
    #
    @73
    @69
    @77
    @71
    @1
    @9
    @9
    sseq1
    @80
    @76
    @70
    @80
    @76
    c0
    @9
    wceq
    @70
    @80
    @75
    c0
    @9
    @80
    @75
    @9
    @9
    cdif
    c0
    @80
    @74
    @9
    @9
    @80
    @74
    @9
    @9
    cin
    @9
    @1
    @9
    @9
    ineq2
    @9
    inidm
    syl6eq
    difeq2d
    @9
    difid
    syl6eq
    eqeq1d
    c0
    @9
    eqcom
    syl6bb
    notbid
    anbi12d
    rspc2ev
    syl112anc
    @67
    @42
    wn
    #
    vs
    @10
    wrex
    @44
    @66
    @81
    vs
    @10
    @13
    @40
    vt
    @10
    rexanali
    rexbii
    @42
    vs
    @10
    rexnal
    sylbb
    syl
    @37
    vs
    vt
    @10
    @10
    @35
    @2
    wss
    @37
    @35
    @0
    @2
    @0
    @1
    inss1
    @0
    @1
    ssun1
    sstri
    @35
    @2
    @9
    sscon
    ax-mp
    rgen2w
    jctil
    rspcedvd
    mprg
end

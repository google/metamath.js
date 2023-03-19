include "cv.mm"
include "cfv.mm"
include "cin.mm"
include "wss.mm"
include "cpw.mm"
include "wral.mm"
include "cun.mm"
include "weq.mm"
include "fveq2.mm"
include "ineq1d.mm"
include "ineq1.mm"
include "fveq2d.mm"
include "sseq12d.mm"
include "ineq2d.mm"
include "ineq2.mm"
include "cbvral2v.mm"
include "cdif.mm"
include "wcel.mm"
include "cvv.mm"
include "ntrclsbex.mm"
include "difssd.mm"
include "sselpwd.mm"
include "adantr.mm"
include "wceq.mm"
include "wrex.mm"
include "elpwi.mm"
include "wa.mm"
include "simpl.mm"
include "simpr.mm"
include "difeq2d.mm"
include "eqeq2d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "dfss4.mm"
include "biimpi.mm"
include "adantl.mm"
include "rspcedvd.mm"
include "syl2an.mm"
include "w3a.mm"
include "simpl1.mm"
include "syl.mm"
include "3ad2antl1.mm"
include "wb.mm"
include "simp13.mm"
include "difundi.mm"
include "syl6eqr.mm"
include "3ad2ant3.mm"
include "cmap.mm"
include "co.mm"
include "simp11.mm"
include "ntrclsiex.mm"
include "jca.mm"
include "wo.mm"
include "wf.mm"
include "elmapi.mm"
include "ffvelrnd.mm"
include "elpwid.mm"
include "orc.mm"
include "inss.mm"
include "3syl.mm"
include "sscon34b.mm"
include "difindi.mm"
include "sseq2i.mm"
include "a1i.mm"
include "simp12.mm"
include "rp-simp2.mm"
include "simpl2.mm"
include "simpl3.mm"
include "eqid.mm"
include "simprl.mm"
include "simprr.mm"
include "unssd.mm"
include "3ad2antl2.mm"
include "dssmapfv3d.mm"
include "ntrclsfv1.mm"
include "fveq1d.mm"
include "eqtr3d.mm"
include "uneq12d.mm"
include "syl32anc.mm"
include "3bitrd.mm"
include "ralxfrd2.mm"
include "syl5bb.mm"

theorem ntrclsk3
  let wph: wff ph
  let vt: setvar t
  let cB: class B
  let cD: class D
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cI: class I
  let cK: class K
  let cO: class O
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  assume ntrcls.o: |- O = ( i e. _V |-> ( k e. ( ~P i ^m ~P i ) |-> ( j e. ~P i |-> ( i \ ( k ` ( i \ j ) ) ) ) ) )
  assume ntrcls.d: |- D = ( O ` B )
  assume ntrcls.r: |- ( ph -> I D K )

  disjoint B s
  disjoint B t
  disjoint s t
  disjoint B i
  disjoint B j
  disjoint B k
  disjoint i j
  disjoint i k
  disjoint i s
  disjoint i t
  disjoint j k
  disjoint j s
  disjoint j t
  disjoint k s
  disjoint k t
  disjoint I s
  disjoint I t
  disjoint I i
  disjoint I j
  disjoint I k
  disjoint ph s
  disjoint ph t
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint B a
  disjoint B b
  disjoint a b
  disjoint a s
  disjoint a t
  disjoint b s
  disjoint b t
  disjoint I a
  disjoint I b
  disjoint K a
  disjoint K b
  disjoint a ph
  disjoint b ph
  assert |- ( ph -> ( A. s e. ~P B A. t e. ~P B ( ( I ` s ) i^i ( I ` t ) ) C_ ( I ` ( s i^i t ) ) <-> A. s e. ~P B A. t e. ~P B ( K ` ( s u. t ) ) C_ ( ( K ` s ) u. ( K ` t ) ) ) )

  proof
    vs
    cv
    #
    cI
    cfv
    #
    vt
    cv
    #
    cI
    cfv
    #
    cin
    #
    @0
    @2
    cin
    #
    cI
    cfv
    #
    wss
    #
    vt
    cB
    cpw
    #
    wral
    vs
    @8
    wral
    va
    cv
    #
    cI
    cfv
    #
    vb
    cv
    #
    cI
    cfv
    #
    cin
    #
    @9
    @11
    cin
    #
    cI
    cfv
    #
    wss
    #
    vb
    @8
    wral
    #
    va
    @8
    wral
    wph
    @0
    @2
    cun
    #
    cK
    cfv
    #
    @0
    cK
    cfv
    #
    @2
    cK
    cfv
    #
    cun
    #
    wss
    #
    vt
    @8
    wral
    #
    vs
    @8
    wral
    @7
    @16
    @10
    @3
    cin
    #
    @9
    @2
    cin
    #
    cI
    cfv
    #
    wss
    vs
    vt
    va
    vb
    @8
    @8
    vs
    va
    weq
    #
    @4
    @25
    @6
    @27
    @28
    @1
    @10
    @3
    @0
    @9
    cI
    fveq2
    ineq1d
    @28
    @5
    @26
    cI
    @0
    @9
    @2
    ineq1
    fveq2d
    sseq12d
    vt
    vb
    weq
    #
    @25
    @13
    @27
    @15
    @29
    @3
    @12
    @10
    @2
    @11
    cI
    fveq2
    ineq2d
    @29
    @26
    @14
    cI
    @2
    @11
    @9
    ineq2
    fveq2d
    sseq12d
    cbvral2v
    wph
    @17
    @24
    va
    vs
    cB
    @0
    cdif
    #
    @8
    @8
    wph
    @30
    @8
    wcel
    @0
    @8
    wcel
    #
    wph
    @30
    cB
    cvv
    wph
    cB
    cD
    cI
    cK
    cO
    ntrcls.d
    ntrcls.r
    ntrclsbex
    #
    wph
    cB
    @0
    difssd
    sselpwd
    adantr
    wph
    cB
    cvv
    wcel
    #
    @9
    cB
    wss
    #
    @9
    @30
    wceq
    #
    vs
    @8
    wrex
    @9
    @8
    wcel
    @32
    @9
    cB
    elpwi
    @33
    @34
    wa
    #
    @35
    cB
    cB
    @9
    cdif
    #
    cdif
    #
    @9
    wceq
    #
    vs
    @37
    @8
    @36
    @37
    cB
    cvv
    @33
    @34
    simpl
    @36
    cB
    @9
    difssd
    sselpwd
    @36
    @0
    @37
    wceq
    #
    wa
    #
    @35
    @9
    @38
    wceq
    @39
    @41
    @30
    @38
    @9
    @41
    @0
    @37
    cB
    @36
    @40
    simpr
    difeq2d
    eqeq2d
    @9
    @38
    eqcom
    syl6bb
    @34
    @39
    @33
    @34
    @39
    @9
    cB
    dfss4
    biimpi
    adantl
    rspcedvd
    syl2an
    wph
    @31
    @35
    w3a
    #
    @16
    @23
    vb
    vt
    cB
    @2
    cdif
    #
    @8
    @8
    @42
    @2
    @8
    wcel
    #
    wa
    wph
    @43
    @8
    wcel
    wph
    @31
    @35
    @44
    simpl1
    wph
    @43
    cB
    cvv
    @32
    wph
    cB
    @2
    difssd
    sselpwd
    syl
    wph
    @31
    @11
    @8
    wcel
    #
    @11
    @43
    wceq
    #
    vt
    @8
    wrex
    #
    @35
    wph
    @33
    @11
    cB
    wss
    #
    @47
    @45
    @32
    @11
    cB
    elpwi
    @33
    @48
    wa
    #
    @46
    cB
    cB
    @11
    cdif
    #
    cdif
    #
    @11
    wceq
    #
    vt
    @50
    @8
    @49
    @50
    cB
    cvv
    @33
    @48
    simpl
    @49
    cB
    @11
    difssd
    sselpwd
    @49
    @2
    @50
    wceq
    #
    wa
    #
    @46
    @11
    @51
    wceq
    @52
    @54
    @43
    @51
    @11
    @54
    @2
    @50
    cB
    @49
    @53
    simpr
    difeq2d
    eqeq2d
    @11
    @51
    eqcom
    syl6bb
    @48
    @52
    @33
    @48
    @52
    @11
    cB
    dfss4
    biimpi
    adantl
    rspcedvd
    syl2an
    3ad2antl1
    @42
    @44
    @46
    w3a
    #
    @16
    @30
    cI
    cfv
    #
    @12
    cin
    #
    @30
    @11
    cin
    #
    cI
    cfv
    #
    wss
    #
    @56
    @43
    cI
    cfv
    #
    cin
    #
    cB
    @18
    cdif
    #
    cI
    cfv
    #
    wss
    #
    @23
    @55
    @35
    @16
    @60
    wb
    wph
    @31
    @35
    @44
    @46
    simp13
    @35
    @13
    @57
    @15
    @59
    @35
    @10
    @56
    @12
    @9
    @30
    cI
    fveq2
    ineq1d
    @35
    @14
    @58
    cI
    @9
    @30
    @11
    ineq1
    fveq2d
    sseq12d
    syl
    @46
    @42
    @60
    @65
    wb
    @44
    @46
    @57
    @62
    @59
    @64
    @46
    @12
    @61
    @56
    @11
    @43
    cI
    fveq2
    ineq2d
    @46
    @58
    @63
    cI
    @46
    @58
    @30
    @43
    cin
    @63
    @11
    @43
    @30
    ineq2
    cB
    @0
    @2
    difundi
    syl6eqr
    fveq2d
    sseq12d
    3ad2ant3
    @55
    @65
    cB
    @64
    cdif
    #
    cB
    @62
    cdif
    #
    wss
    #
    @66
    cB
    @56
    cdif
    #
    cB
    @61
    cdif
    #
    cun
    #
    wss
    #
    @23
    @55
    cI
    @8
    @8
    cmap
    co
    wcel
    #
    @33
    wa
    #
    @62
    cB
    wss
    #
    @64
    cB
    wss
    #
    wa
    @65
    @68
    wb
    @55
    wph
    @74
    wph
    @31
    @35
    @44
    @46
    simp11
    #
    wph
    @73
    @33
    wph
    cB
    cD
    vi
    vj
    vk
    cI
    cK
    cO
    ntrcls.o
    ntrcls.d
    ntrcls.r
    ntrclsiex
    #
    @32
    jca
    syl
    @74
    @75
    @76
    @74
    @56
    cB
    wss
    #
    @79
    @61
    cB
    wss
    #
    wo
    @75
    @74
    @56
    cB
    @74
    @8
    @8
    @30
    cI
    @73
    @8
    @8
    cI
    wf
    @33
    cI
    @8
    @8
    elmapi
    adantr
    #
    @74
    @30
    cB
    cvv
    @73
    @33
    simpr
    #
    @74
    cB
    @0
    difssd
    sselpwd
    ffvelrnd
    elpwid
    @79
    @80
    orc
    @56
    @61
    cB
    inss
    3syl
    @74
    @64
    cB
    @74
    @8
    @8
    @63
    cI
    @81
    @74
    @63
    cB
    cvv
    @82
    @74
    cB
    @18
    difssd
    sselpwd
    ffvelrnd
    elpwid
    jca
    @62
    @64
    cB
    sscon34b
    3syl
    @68
    @72
    wb
    @55
    @67
    @71
    @66
    cB
    @56
    @61
    difindi
    sseq2i
    a1i
    @55
    wph
    @33
    @73
    @31
    @44
    @72
    @23
    wb
    @77
    @55
    wph
    @33
    @77
    @32
    syl
    @55
    wph
    @73
    @77
    @78
    syl
    wph
    @31
    @35
    @44
    @46
    simp12
    @42
    @44
    @46
    rp-simp2
    wph
    @33
    @73
    w3a
    #
    @31
    @44
    wa
    #
    wa
    #
    @66
    @19
    @71
    @22
    @85
    @18
    cI
    cD
    cfv
    #
    cfv
    #
    @66
    @19
    @85
    cB
    cD
    @18
    @87
    vk
    cI
    @86
    cO
    cvv
    vj
    vi
    ntrcls.o
    ntrcls.d
    wph
    @33
    @73
    @84
    simpl2
    #
    wph
    @33
    @73
    @84
    simpl3
    #
    @86
    eqid
    #
    @33
    wph
    @84
    @18
    @8
    wcel
    @73
    @33
    @84
    wa
    #
    @18
    cB
    cvv
    @33
    @84
    simpl
    @91
    @0
    @2
    cB
    @91
    @0
    cB
    @33
    @31
    @44
    simprl
    elpwid
    @91
    @2
    cB
    @33
    @31
    @44
    simprr
    elpwid
    unssd
    sselpwd
    3ad2antl2
    @87
    eqid
    dssmapfv3d
    @85
    wph
    @87
    @19
    wceq
    wph
    @33
    @73
    @84
    simpl1
    #
    wph
    @18
    @86
    cK
    wph
    cB
    cD
    vi
    vj
    vk
    cI
    cK
    cO
    ntrcls.o
    ntrcls.d
    ntrcls.r
    ntrclsfv1
    #
    fveq1d
    syl
    eqtr3d
    @85
    @69
    @20
    @70
    @21
    @85
    @0
    @86
    cfv
    #
    @69
    @20
    @85
    cB
    cD
    @0
    @94
    vk
    cI
    @86
    cO
    cvv
    vj
    vi
    ntrcls.o
    ntrcls.d
    @88
    @89
    @90
    @83
    @31
    @44
    simprl
    @94
    eqid
    dssmapfv3d
    @85
    wph
    @94
    @20
    wceq
    @92
    wph
    @0
    @86
    cK
    @93
    fveq1d
    syl
    eqtr3d
    @85
    @2
    @86
    cfv
    #
    @70
    @21
    @85
    cB
    cD
    @2
    @95
    vk
    cI
    @86
    cO
    cvv
    vj
    vi
    ntrcls.o
    ntrcls.d
    @88
    @89
    @90
    @83
    @31
    @44
    simprr
    @95
    eqid
    dssmapfv3d
    @85
    wph
    @95
    @21
    wceq
    @92
    wph
    @2
    @86
    cK
    @93
    fveq1d
    syl
    eqtr3d
    uneq12d
    sseq12d
    syl32anc
    3bitrd
    3bitrd
    ralxfrd2
    ralxfrd2
    syl5bb
end

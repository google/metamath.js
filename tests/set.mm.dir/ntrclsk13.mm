include "cv.mm"
include "cin.mm"
include "cfv.mm"
include "wceq.mm"
include "cpw.mm"
include "wral.mm"
include "cun.mm"
include "weq.mm"
include "ineq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "ineq1d.mm"
include "eqeq12d.mm"
include "ineq2.mm"
include "ineq2d.mm"
include "cbvral2v.mm"
include "cdif.mm"
include "wcel.mm"
include "cvv.mm"
include "ntrclsbex.mm"
include "difssd.mm"
include "sselpwd.mm"
include "adantr.mm"
include "wss.mm"
include "wrex.mm"
include "elpwi.mm"
include "wa.mm"
include "wb.mm"
include "difeq2.mm"
include "eqeq2d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "adantl.mm"
include "dfss4.mm"
include "biimpi.mm"
include "rspcedvd.mm"
include "sylan2.mm"
include "w3a.mm"
include "ralbidv.mm"
include "3ad2ant3.mm"
include "ad2antrr.mm"
include "simpll.mm"
include "syl2anc.mm"
include "difundi.mm"
include "syl6eqr.mm"
include "simp1l.mm"
include "jccir.mm"
include "simp1r.mm"
include "simp2.mm"
include "wf.mm"
include "cmap.mm"
include "co.mm"
include "ntrclsiex.mm"
include "elmapi.mm"
include "syl.mm"
include "anim1i.mm"
include "simpl.mm"
include "simpr.mm"
include "ffvelrnd.mm"
include "elpwid.mm"
include "ssinss1.mm"
include "jca.mm"
include "rcompleq.mm"
include "3syl.mm"
include "simplr.mm"
include "eqid.mm"
include "simprl.mm"
include "simprr.mm"
include "unssd.mm"
include "dssmapfv3d.mm"
include "uneq12d.mm"
include "difindi.mm"
include "ntrclsfv1.mm"
include "fveq1.mm"
include "3bitr2d.mm"
include "syl12anc.mm"
include "bitrd.mm"
include "ralxfrd2.mm"
include "3adant3.mm"
include "syl5bb.mm"

theorem ntrclsk13
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
  assert |- ( ph -> ( A. s e. ~P B A. t e. ~P B ( I ` ( s i^i t ) ) = ( ( I ` s ) i^i ( I ` t ) ) <-> A. s e. ~P B A. t e. ~P B ( K ` ( s u. t ) ) = ( ( K ` s ) u. ( K ` t ) ) ) )

  proof
    vs
    cv
    #
    vt
    cv
    #
    cin
    #
    cI
    cfv
    #
    @0
    cI
    cfv
    #
    @1
    cI
    cfv
    #
    cin
    #
    wceq
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
    vb
    cv
    #
    cin
    #
    cI
    cfv
    #
    @9
    cI
    cfv
    #
    @10
    cI
    cfv
    #
    cin
    #
    wceq
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
    @1
    cun
    #
    cK
    cfv
    #
    @0
    cK
    cfv
    #
    @1
    cK
    cfv
    #
    cun
    #
    wceq
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
    @9
    @1
    cin
    #
    cI
    cfv
    #
    @13
    @5
    cin
    #
    wceq
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
    @3
    @26
    @6
    @27
    @28
    @2
    @25
    cI
    @0
    @9
    @1
    ineq1
    fveq2d
    @28
    @4
    @13
    @5
    @0
    @9
    cI
    fveq2
    ineq1d
    eqeq12d
    vt
    vb
    weq
    #
    @26
    @12
    @27
    @15
    @29
    @25
    @11
    cI
    @1
    @10
    @9
    ineq2
    fveq2d
    @29
    @5
    @14
    @13
    @1
    @10
    cI
    fveq2
    ineq2d
    eqeq12d
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
    @9
    @8
    wcel
    wph
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
    cB
    elpwi
    wph
    @33
    wa
    #
    @34
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
    @36
    @8
    @35
    @36
    cB
    cvv
    wph
    cB
    cvv
    wcel
    #
    @33
    @32
    adantr
    @35
    cB
    @9
    difssd
    sselpwd
    @0
    @36
    wceq
    #
    @34
    @38
    wb
    @35
    @40
    @34
    @9
    @37
    wceq
    @38
    @40
    @30
    @37
    @9
    @0
    @36
    cB
    difeq2
    eqeq2d
    @9
    @37
    eqcom
    syl6bb
    adantl
    @33
    @38
    wph
    @33
    @38
    @9
    cB
    dfss4
    biimpi
    adantl
    rspcedvd
    sylan2
    wph
    @31
    @34
    w3a
    @17
    @30
    @10
    cin
    #
    cI
    cfv
    #
    @30
    cI
    cfv
    #
    @14
    cin
    #
    wceq
    #
    vb
    @8
    wral
    #
    @24
    @34
    wph
    @17
    @46
    wb
    @31
    @34
    @16
    @45
    vb
    @8
    @34
    @12
    @42
    @15
    @44
    @34
    @11
    @41
    cI
    @9
    @30
    @10
    ineq1
    fveq2d
    @34
    @13
    @43
    @14
    @9
    @30
    cI
    fveq2
    ineq1d
    eqeq12d
    ralbidv
    3ad2ant3
    wph
    @31
    @46
    @24
    wb
    @34
    wph
    @31
    wa
    #
    @45
    @23
    vb
    vt
    cB
    @1
    cdif
    #
    @8
    @8
    wph
    @48
    @8
    wcel
    @31
    @1
    @8
    wcel
    #
    wph
    @48
    cB
    cvv
    @32
    wph
    cB
    @1
    difssd
    sselpwd
    ad2antrr
    @47
    @10
    @8
    wcel
    #
    wa
    wph
    @10
    cB
    wss
    #
    @10
    @48
    wceq
    #
    vt
    @8
    wrex
    wph
    @31
    @50
    simpll
    @50
    @51
    @47
    @10
    cB
    elpwi
    adantl
    wph
    @51
    wa
    #
    @52
    cB
    cB
    @10
    cdif
    #
    cdif
    #
    @10
    wceq
    #
    vt
    @54
    @8
    wph
    @54
    @8
    wcel
    @51
    wph
    @54
    cB
    cvv
    @32
    wph
    cB
    @10
    difssd
    sselpwd
    adantr
    @1
    @54
    wceq
    #
    @52
    @56
    wb
    @53
    @57
    @52
    @10
    @55
    wceq
    @56
    @57
    @48
    @55
    @10
    @1
    @54
    cB
    difeq2
    eqeq2d
    @10
    @55
    eqcom
    syl6bb
    adantl
    @51
    @56
    wph
    @51
    @56
    @10
    cB
    dfss4
    biimpi
    adantl
    rspcedvd
    syl2anc
    @47
    @49
    @52
    w3a
    #
    @45
    cB
    @18
    cdif
    #
    cI
    cfv
    #
    @43
    @48
    cI
    cfv
    #
    cin
    #
    wceq
    #
    @23
    @52
    @47
    @45
    @63
    wb
    @49
    @52
    @42
    @60
    @44
    @62
    @52
    @41
    @59
    cI
    @52
    @41
    @30
    @48
    cin
    @59
    @10
    @48
    @30
    ineq2
    cB
    @0
    @1
    difundi
    syl6eqr
    fveq2d
    @52
    @14
    @61
    @43
    @10
    @48
    cI
    fveq2
    ineq2d
    eqeq12d
    3ad2ant3
    @58
    wph
    @39
    wa
    #
    @31
    @49
    @63
    @23
    wb
    @58
    wph
    @39
    wph
    @31
    @49
    @52
    simp1l
    @32
    jccir
    wph
    @31
    @49
    @52
    simp1r
    @47
    @49
    @52
    simp2
    @64
    @31
    @49
    wa
    #
    wa
    #
    @63
    cB
    @60
    cdif
    #
    cB
    @62
    cdif
    #
    wceq
    #
    @18
    cI
    cD
    cfv
    #
    cfv
    #
    @0
    @70
    cfv
    #
    @1
    @70
    cfv
    #
    cun
    #
    wceq
    #
    @23
    @66
    @8
    @8
    cI
    wf
    #
    @39
    wa
    #
    @60
    cB
    wss
    #
    @62
    cB
    wss
    #
    wa
    @63
    @69
    wb
    @64
    @77
    @65
    wph
    @76
    @39
    wph
    cI
    @8
    @8
    cmap
    co
    wcel
    #
    @76
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
    cI
    @8
    @8
    elmapi
    syl
    anim1i
    adantr
    @77
    @78
    @79
    @77
    @60
    cB
    @77
    @8
    @8
    @59
    cI
    @76
    @39
    simpl
    #
    @77
    @59
    cB
    cvv
    @76
    @39
    simpr
    #
    @77
    cB
    @18
    difssd
    sselpwd
    ffvelrnd
    elpwid
    @77
    @43
    cB
    wss
    @79
    @77
    @43
    cB
    @77
    @8
    @8
    @30
    cI
    @82
    @77
    @30
    cB
    cvv
    @83
    @77
    cB
    @0
    difssd
    sselpwd
    ffvelrnd
    elpwid
    @43
    @61
    cB
    ssinss1
    syl
    jca
    @60
    @62
    cB
    rcompleq
    3syl
    @66
    @71
    @67
    @74
    @68
    @66
    cB
    cD
    @18
    @71
    vk
    cI
    @70
    cO
    cvv
    vj
    vi
    ntrcls.o
    ntrcls.d
    wph
    @39
    @65
    simplr
    #
    wph
    @80
    @39
    @65
    @81
    ad2antrr
    @70
    eqid
    #
    @66
    @18
    cB
    cvv
    @84
    @66
    @0
    @1
    cB
    @66
    @0
    cB
    @64
    @31
    @49
    simprl
    elpwid
    @66
    @1
    cB
    @64
    @31
    @49
    simprr
    elpwid
    unssd
    sselpwd
    @71
    eqid
    dssmapfv3d
    @66
    @74
    cB
    @43
    cdif
    #
    cB
    @61
    cdif
    #
    cun
    @68
    @66
    @72
    @86
    @73
    @87
    @65
    @64
    @31
    @72
    @86
    wceq
    @31
    @49
    simpl
    @64
    @31
    wa
    cB
    cD
    @0
    @72
    vk
    cI
    @70
    cO
    cvv
    vj
    vi
    ntrcls.o
    ntrcls.d
    wph
    @39
    @31
    simplr
    wph
    @80
    @39
    @31
    @81
    ad2antrr
    @85
    @64
    @31
    simpr
    @72
    eqid
    dssmapfv3d
    sylan2
    @65
    @64
    @49
    @73
    @87
    wceq
    @31
    @49
    simpr
    @64
    @49
    wa
    cB
    cD
    @1
    @73
    vk
    cI
    @70
    cO
    cvv
    vj
    vi
    ntrcls.o
    ntrcls.d
    wph
    @39
    @49
    simplr
    wph
    @80
    @39
    @49
    @81
    ad2antrr
    @85
    @64
    @49
    simpr
    @73
    eqid
    dssmapfv3d
    sylan2
    uneq12d
    cB
    @43
    @61
    difindi
    syl6eqr
    eqeq12d
    @66
    wph
    @70
    cK
    wceq
    #
    @75
    @23
    wb
    wph
    @39
    @65
    simpll
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
    @88
    @71
    @19
    @74
    @22
    @18
    @70
    cK
    fveq1
    @88
    @72
    @20
    @73
    @21
    @0
    @70
    cK
    fveq1
    @1
    @70
    cK
    fveq1
    uneq12d
    eqeq12d
    3syl
    3bitr2d
    syl12anc
    bitrd
    ralxfrd2
    3adant3
    bitrd
    ralxfrd2
    syl5bb
end

include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cfv.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "cun.mm"
include "weq.mm"
include "ineq1.mm"
include "eqeq1d.mm"
include "fveq2.mm"
include "ineq1d.mm"
include "imbi12d.mm"
include "ineq2.mm"
include "ineq2d.mm"
include "cbvral2v.mm"
include "cdif.mm"
include "wcel.mm"
include "ntrclsrcomplex.mm"
include "adantr.mm"
include "wa.mm"
include "wb.mm"
include "difeq2.mm"
include "eqeq2d.mm"
include "adantl.mm"
include "wss.mm"
include "elpwi.mm"
include "dfss4.mm"
include "sylib.mm"
include "eqcomd.mm"
include "rspcedvd.mm"
include "w3a.mm"
include "simpl1.mm"
include "syl.mm"
include "wrex.mm"
include "3ad2antl1.mm"
include "simp13.mm"
include "simp3.mm"
include "simp11.mm"
include "simp12.mm"
include "simp2.mm"
include "elpwid.mm"
include "unssd.mm"
include "ssid.mm"
include "rcompleq.mm"
include "sylancl.mm"
include "difundi.mm"
include "difid.mm"
include "eqeq12i.mm"
include "syl6rbb.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "ntrclsiex.mm"
include "3ad2ant1.mm"
include "elmapi.mm"
include "cvv.mm"
include "ntrclsbex.mm"
include "difssd.mm"
include "sselpwd.mm"
include "ffvelrnd.mm"
include "ssinss1.mm"
include "0ss.mm"
include "difindi.mm"
include "dif0.mm"
include "syl6bb.mm"
include "eqid.mm"
include "dssmapfv3d.mm"
include "uneq12d.mm"
include "ntrclsfv1.mm"
include "fveq1.mm"
include "eqtr3d.mm"
include "imbi2d.mm"
include "bitrd.mm"
include "syl3anc.mm"
include "3bitrd.mm"
include "ralxfrd2.mm"
include "syl5bb.mm"

theorem ntrclskb
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
  assert |- ( ph -> ( A. s e. ~P B A. t e. ~P B ( ( s i^i t ) = (/) -> ( ( I ` s ) i^i ( I ` t ) ) = (/) ) <-> A. s e. ~P B A. t e. ~P B ( ( s u. t ) = B -> ( ( K ` s ) u. ( K ` t ) ) = B ) ) )

  proof
    vs
    cv
    #
    vt
    cv
    #
    cin
    #
    c0
    wceq
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
    c0
    wceq
    #
    wi
    #
    vt
    cB
    cpw
    #
    wral
    vs
    @9
    wral
    va
    cv
    #
    vb
    cv
    #
    cin
    #
    c0
    wceq
    #
    @10
    cI
    cfv
    #
    @11
    cI
    cfv
    #
    cin
    #
    c0
    wceq
    #
    wi
    #
    vb
    @9
    wral
    #
    va
    @9
    wral
    wph
    @0
    @1
    cun
    #
    cB
    wceq
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
    cB
    wceq
    #
    wi
    #
    vt
    @9
    wral
    #
    vs
    @9
    wral
    @8
    @18
    @10
    @1
    cin
    #
    c0
    wceq
    #
    @14
    @5
    cin
    #
    c0
    wceq
    #
    wi
    vs
    vt
    va
    vb
    @9
    @9
    vs
    va
    weq
    #
    @3
    @29
    @7
    @31
    @32
    @2
    @28
    c0
    @0
    @10
    @1
    ineq1
    eqeq1d
    @32
    @6
    @30
    c0
    @32
    @4
    @14
    @5
    @0
    @10
    cI
    fveq2
    ineq1d
    eqeq1d
    imbi12d
    vt
    vb
    weq
    #
    @29
    @13
    @31
    @17
    @33
    @28
    @12
    c0
    @1
    @11
    @10
    ineq2
    eqeq1d
    @33
    @30
    @16
    c0
    @33
    @5
    @15
    @14
    @1
    @11
    cI
    fveq2
    ineq2d
    eqeq1d
    imbi12d
    cbvral2v
    wph
    @19
    @27
    va
    vs
    cB
    @0
    cdif
    #
    @9
    @9
    wph
    @34
    @9
    wcel
    @0
    @9
    wcel
    #
    wph
    cB
    cD
    @0
    cI
    cK
    cO
    ntrcls.d
    ntrcls.r
    ntrclsrcomplex
    adantr
    wph
    @10
    @9
    wcel
    #
    wa
    #
    @10
    @34
    wceq
    #
    @10
    cB
    cB
    @10
    cdif
    #
    cdif
    #
    wceq
    #
    vs
    @39
    @9
    wph
    @39
    @9
    wcel
    @36
    wph
    cB
    cD
    @10
    cI
    cK
    cO
    ntrcls.d
    ntrcls.r
    ntrclsrcomplex
    adantr
    @0
    @39
    wceq
    #
    @38
    @41
    wb
    @37
    @42
    @34
    @40
    @10
    @0
    @39
    cB
    difeq2
    eqeq2d
    adantl
    @36
    @41
    wph
    @36
    @40
    @10
    @36
    @10
    cB
    wss
    @40
    @10
    wceq
    @10
    cB
    elpwi
    @10
    cB
    dfss4
    sylib
    eqcomd
    adantl
    rspcedvd
    wph
    @35
    @38
    w3a
    #
    @18
    @26
    vb
    vt
    cB
    @1
    cdif
    #
    @9
    @9
    @43
    @1
    @9
    wcel
    #
    wa
    wph
    @44
    @9
    wcel
    wph
    @35
    @38
    @45
    simpl1
    wph
    cB
    cD
    @1
    cI
    cK
    cO
    ntrcls.d
    ntrcls.r
    ntrclsrcomplex
    syl
    wph
    @35
    @11
    @9
    wcel
    #
    @11
    @44
    wceq
    #
    vt
    @9
    wrex
    @38
    wph
    @46
    wa
    #
    @47
    @11
    cB
    cB
    @11
    cdif
    #
    cdif
    #
    wceq
    #
    vt
    @49
    @9
    wph
    @49
    @9
    wcel
    @46
    wph
    cB
    cD
    @11
    cI
    cK
    cO
    ntrcls.d
    ntrcls.r
    ntrclsrcomplex
    adantr
    @1
    @49
    wceq
    #
    @47
    @51
    wb
    @48
    @52
    @44
    @50
    @11
    @1
    @49
    cB
    difeq2
    eqeq2d
    adantl
    @46
    @51
    wph
    @46
    @50
    @11
    @46
    @11
    cB
    wss
    @50
    @11
    wceq
    @11
    cB
    elpwi
    @11
    cB
    dfss4
    sylib
    eqcomd
    adantl
    rspcedvd
    3ad2antl1
    @43
    @45
    @47
    w3a
    #
    @18
    @34
    @11
    cin
    #
    c0
    wceq
    #
    @34
    cI
    cfv
    #
    @15
    cin
    #
    c0
    wceq
    #
    wi
    #
    @34
    @44
    cin
    #
    c0
    wceq
    #
    @56
    @44
    cI
    cfv
    #
    cin
    #
    c0
    wceq
    #
    wi
    #
    @26
    @53
    @38
    @18
    @59
    wb
    wph
    @35
    @38
    @45
    @47
    simp13
    @38
    @13
    @55
    @17
    @58
    @38
    @12
    @54
    c0
    @10
    @34
    @11
    ineq1
    eqeq1d
    @38
    @16
    @57
    c0
    @38
    @14
    @56
    @15
    @10
    @34
    cI
    fveq2
    ineq1d
    eqeq1d
    imbi12d
    syl
    @53
    @47
    @59
    @65
    wb
    @43
    @45
    @47
    simp3
    @47
    @55
    @61
    @58
    @64
    @47
    @54
    @60
    c0
    @11
    @44
    @34
    ineq2
    eqeq1d
    @47
    @57
    @63
    c0
    @47
    @15
    @62
    @56
    @11
    @44
    cI
    fveq2
    ineq2d
    eqeq1d
    imbi12d
    syl
    @53
    wph
    @35
    @45
    @65
    @26
    wb
    wph
    @35
    @38
    @45
    @47
    simp11
    wph
    @35
    @38
    @45
    @47
    simp12
    @43
    @45
    @47
    simp2
    wph
    @35
    @45
    w3a
    #
    @65
    @21
    cB
    @56
    cdif
    #
    cB
    @62
    cdif
    #
    cun
    #
    cB
    wceq
    #
    wi
    @26
    @66
    @61
    @21
    @64
    @70
    @66
    @21
    cB
    @20
    cdif
    #
    cB
    cB
    cdif
    #
    wceq
    #
    @61
    @66
    @20
    cB
    wss
    cB
    cB
    wss
    @21
    @73
    wb
    @66
    @0
    @1
    cB
    @66
    @0
    cB
    wph
    @35
    @45
    simp2
    #
    elpwid
    @66
    @1
    cB
    wph
    @35
    @45
    simp3
    #
    elpwid
    unssd
    cB
    ssid
    @20
    cB
    cB
    rcompleq
    sylancl
    @71
    @60
    @72
    c0
    cB
    @0
    @1
    difundi
    cB
    difid
    eqeq12i
    syl6rbb
    @66
    @64
    cB
    @63
    cdif
    #
    cB
    c0
    cdif
    #
    wceq
    #
    @70
    @66
    @63
    cB
    wss
    #
    c0
    cB
    wss
    @64
    @78
    wb
    @66
    @56
    cB
    wss
    @79
    @66
    @56
    cB
    @66
    @9
    @9
    @34
    cI
    @66
    cI
    @9
    @9
    cmap
    co
    wcel
    #
    @9
    @9
    cI
    wf
    wph
    @35
    @80
    @45
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
    3ad2ant1
    #
    cI
    @9
    @9
    elmapi
    syl
    @66
    @34
    cB
    cvv
    wph
    @35
    cB
    cvv
    wcel
    @45
    wph
    cB
    cD
    cI
    cK
    cO
    ntrcls.d
    ntrcls.r
    ntrclsbex
    3ad2ant1
    #
    @66
    cB
    @0
    difssd
    sselpwd
    ffvelrnd
    elpwid
    @56
    @62
    cB
    ssinss1
    syl
    cB
    0ss
    @63
    c0
    cB
    rcompleq
    sylancl
    @76
    @69
    @77
    cB
    cB
    @56
    @62
    difindi
    cB
    dif0
    eqeq12i
    syl6bb
    imbi12d
    @66
    @70
    @25
    @21
    @66
    @69
    @24
    cB
    @66
    @0
    cI
    cD
    cfv
    #
    cfv
    #
    @1
    @83
    cfv
    #
    cun
    #
    @69
    @24
    @66
    @84
    @67
    @85
    @68
    @66
    cB
    cD
    @0
    @84
    vk
    cI
    @83
    cO
    cvv
    vj
    vi
    ntrcls.o
    ntrcls.d
    @82
    @81
    @83
    eqid
    #
    @74
    @84
    eqid
    dssmapfv3d
    @66
    cB
    cD
    @1
    @85
    vk
    cI
    @83
    cO
    cvv
    vj
    vi
    ntrcls.o
    ntrcls.d
    @82
    @81
    @87
    @75
    @85
    eqid
    dssmapfv3d
    uneq12d
    @66
    @83
    cK
    wceq
    #
    @86
    @24
    wceq
    wph
    @35
    @88
    @45
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
    3ad2ant1
    @88
    @84
    @22
    @85
    @23
    @0
    @83
    cK
    fveq1
    @1
    @83
    cK
    fveq1
    uneq12d
    syl
    eqtr3d
    eqeq1d
    imbi2d
    bitrd
    syl3anc
    3bitrd
    ralxfrd2
    ralxfrd2
    syl5bb
end

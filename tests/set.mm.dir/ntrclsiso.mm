include "cv.mm"
include "wss.mm"
include "cfv.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "weq.mm"
include "sseq1.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "imbi12d.mm"
include "sseq2.mm"
include "sseq2d.mm"
include "cbvral2v.mm"
include "ralcom.mm"
include "bitri.mm"
include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "simpl.mm"
include "ntrclsbex.mm"
include "syl.mm"
include "difssd.mm"
include "sselpwd.mm"
include "wceq.mm"
include "wrex.mm"
include "elpwi.mm"
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
include "3ad2antl1.mm"
include "wb.mm"
include "simp12.mm"
include "elpwid.mm"
include "simp2.mm"
include "sscon34b.mm"
include "syl2anc.mm"
include "bicomd.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "simp11.mm"
include "ntrclsiex.mm"
include "elmapi.mm"
include "ffvelrnd.mm"
include "simp3.mm"
include "simp13.mm"
include "sseq12d.mm"
include "fveq2d.mm"
include "ntrclsfv1.mm"
include "fveq1d.mm"
include "eqid.mm"
include "dssmapfv3d.mm"
include "eqtr3d.mm"
include "wbr.mm"
include "imbi2d.mm"
include "3bitr4d.mm"
include "ralxfrd2.mm"
include "syl5bb.mm"

theorem ntrclsiso
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

  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B s
  disjoint B t
  disjoint i j
  disjoint i k
  disjoint i s
  disjoint i t
  disjoint j k
  disjoint j s
  disjoint j t
  disjoint k s
  disjoint k t
  disjoint s t
  disjoint I j
  disjoint I k
  disjoint I s
  disjoint I t
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint ph s
  disjoint ph t
  disjoint B a
  disjoint B b
  disjoint a b
  disjoint a i
  disjoint a j
  disjoint a k
  disjoint a s
  disjoint a t
  disjoint b i
  disjoint b j
  disjoint b k
  disjoint b s
  disjoint b t
  disjoint I a
  disjoint I b
  disjoint K a
  disjoint K b
  disjoint a ph
  disjoint b ph
  assert |- ( ph -> ( A. s e. ~P B A. t e. ~P B ( s C_ t -> ( I ` s ) C_ ( I ` t ) ) <-> A. s e. ~P B A. t e. ~P B ( s C_ t -> ( K ` s ) C_ ( K ` t ) ) ) )

  proof
    vs
    cv
    #
    vt
    cv
    #
    wss
    #
    @0
    cI
    cfv
    #
    @1
    cI
    cfv
    #
    wss
    #
    wi
    #
    vt
    cB
    cpw
    #
    wral
    vs
    @7
    wral
    #
    vb
    cv
    #
    va
    cv
    #
    wss
    #
    @9
    cI
    cfv
    #
    @10
    cI
    cfv
    #
    wss
    #
    wi
    #
    vb
    @7
    wral
    #
    va
    @7
    wral
    #
    wph
    @2
    @0
    cK
    cfv
    #
    @1
    cK
    cfv
    #
    wss
    #
    wi
    #
    vt
    @7
    wral
    #
    vs
    @7
    wral
    @8
    @15
    va
    @7
    wral
    vb
    @7
    wral
    @17
    @6
    @15
    @9
    @1
    wss
    #
    @12
    @4
    wss
    #
    wi
    vs
    vt
    vb
    va
    @7
    @7
    vs
    vb
    weq
    #
    @2
    @23
    @5
    @24
    @0
    @9
    @1
    sseq1
    @25
    @3
    @12
    @4
    @0
    @9
    cI
    fveq2
    sseq1d
    imbi12d
    vt
    va
    weq
    #
    @23
    @11
    @24
    @14
    @1
    @10
    @9
    sseq2
    @26
    @4
    @13
    @12
    @1
    @10
    cI
    fveq2
    sseq2d
    imbi12d
    cbvral2v
    @15
    vb
    va
    @7
    @7
    ralcom
    bitri
    wph
    @16
    @22
    va
    vs
    cB
    @0
    cdif
    #
    @7
    @7
    wph
    @0
    @7
    wcel
    #
    wa
    #
    @27
    cB
    cvv
    @29
    wph
    cB
    cvv
    wcel
    #
    wph
    @28
    simpl
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
    syl
    @29
    cB
    @0
    difssd
    sselpwd
    wph
    @30
    @10
    cB
    wss
    #
    @10
    @27
    wceq
    #
    vs
    @7
    wrex
    @10
    @7
    wcel
    @31
    @10
    cB
    elpwi
    @30
    @32
    wa
    #
    @33
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
    vs
    @35
    @7
    @34
    @35
    cB
    cvv
    @30
    @32
    simpl
    @34
    cB
    @10
    difssd
    sselpwd
    @34
    @0
    @35
    wceq
    #
    wa
    #
    @33
    @10
    @36
    wceq
    @37
    @39
    @27
    @36
    @10
    @39
    @0
    @35
    cB
    @34
    @38
    simpr
    difeq2d
    eqeq2d
    @10
    @36
    eqcom
    syl6bb
    @32
    @37
    @30
    @32
    @37
    @10
    cB
    dfss4
    biimpi
    adantl
    rspcedvd
    syl2an
    wph
    @28
    @33
    w3a
    #
    @15
    @21
    vb
    vt
    cB
    @1
    cdif
    #
    @7
    @7
    @40
    @1
    @7
    wcel
    #
    wa
    #
    @41
    cB
    cvv
    @43
    wph
    @30
    wph
    @28
    @33
    @42
    simpl1
    @31
    syl
    @43
    cB
    @1
    difssd
    sselpwd
    wph
    @28
    @9
    @7
    wcel
    #
    @9
    @41
    wceq
    #
    vt
    @7
    wrex
    #
    @33
    wph
    @30
    @9
    cB
    wss
    #
    @46
    @44
    @31
    @9
    cB
    elpwi
    @30
    @47
    wa
    #
    @45
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
    vt
    @49
    @7
    @48
    @49
    cB
    cvv
    @30
    @47
    simpl
    @48
    cB
    @9
    difssd
    sselpwd
    @48
    @1
    @49
    wceq
    #
    wa
    #
    @45
    @9
    @50
    wceq
    @51
    @53
    @41
    @50
    @9
    @53
    @1
    @49
    cB
    @48
    @52
    simpr
    difeq2d
    eqeq2d
    @9
    @50
    eqcom
    syl6bb
    @47
    @51
    @30
    @47
    @51
    @9
    cB
    dfss4
    biimpi
    adantl
    rspcedvd
    syl2an
    3ad2antl1
    @40
    @42
    @45
    w3a
    #
    @41
    @27
    wss
    #
    @41
    cI
    cfv
    #
    @27
    cI
    cfv
    #
    wss
    #
    wi
    @2
    cB
    @57
    cdif
    #
    cB
    @56
    cdif
    #
    wss
    #
    wi
    @15
    @21
    @54
    @55
    @2
    @58
    @61
    @54
    @2
    @55
    @54
    @0
    cB
    wss
    @1
    cB
    wss
    @2
    @55
    wb
    @54
    @0
    cB
    wph
    @28
    @33
    @42
    @45
    simp12
    #
    elpwid
    @54
    @1
    cB
    @40
    @42
    @45
    simp2
    #
    elpwid
    @0
    @1
    cB
    sscon34b
    syl2anc
    bicomd
    @54
    @56
    cB
    wss
    @57
    cB
    wss
    @58
    @61
    wb
    @54
    @56
    cB
    @54
    @7
    @7
    @41
    cI
    @54
    cI
    @7
    @7
    cmap
    co
    wcel
    #
    @7
    @7
    cI
    wf
    @54
    wph
    @64
    wph
    @28
    @33
    @42
    @45
    simp11
    #
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
    syl
    #
    cI
    @7
    @7
    elmapi
    syl
    #
    @54
    @41
    cB
    cvv
    @54
    wph
    @30
    @65
    @31
    syl
    #
    @54
    cB
    @1
    difssd
    sselpwd
    ffvelrnd
    elpwid
    @54
    @57
    cB
    @54
    @7
    @7
    @27
    cI
    @67
    @54
    @27
    cB
    cvv
    @68
    @54
    cB
    @0
    difssd
    sselpwd
    ffvelrnd
    elpwid
    @56
    @57
    cB
    sscon34b
    syl2anc
    imbi12d
    @54
    @11
    @55
    @14
    @58
    @54
    @9
    @41
    @10
    @27
    @40
    @42
    @45
    simp3
    #
    wph
    @28
    @33
    @42
    @45
    simp13
    #
    sseq12d
    @54
    @12
    @56
    @13
    @57
    @54
    @9
    @41
    cI
    @69
    fveq2d
    @54
    @10
    @27
    cI
    @70
    fveq2d
    sseq12d
    imbi12d
    @54
    @20
    @61
    @2
    @54
    @18
    @59
    @19
    @60
    @54
    @0
    cI
    cD
    cfv
    #
    cfv
    #
    @18
    @59
    @54
    @0
    @71
    cK
    @54
    wph
    @71
    cK
    wceq
    @65
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
    syl
    fveq1d
    @54
    cB
    cD
    @0
    @72
    vk
    cI
    @71
    cO
    cvv
    vj
    vi
    ntrcls.o
    ntrcls.d
    @68
    @66
    @71
    eqid
    #
    @62
    @72
    eqid
    dssmapfv3d
    eqtr3d
    @54
    @1
    @71
    cfv
    #
    @19
    @60
    @54
    @1
    @71
    cK
    @54
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
    @54
    wph
    cI
    cK
    cD
    wbr
    @65
    ntrcls.r
    syl
    ntrclsfv1
    fveq1d
    @54
    cB
    cD
    @1
    @74
    vk
    cI
    @71
    cO
    cvv
    vj
    vi
    ntrcls.o
    ntrcls.d
    @68
    @66
    @73
    @63
    @74
    eqid
    dssmapfv3d
    eqtr3d
    sseq12d
    imbi2d
    3bitr4d
    ralxfrd2
    ralxfrd2
    syl5bb
end

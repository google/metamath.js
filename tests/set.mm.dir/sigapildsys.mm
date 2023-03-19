include "csiga.mm"
include "cfv.mm"
include "cin.mm"
include "sigapisys.mm"
include "sigaldsys.mm"
include "ssini.mm"
include "cv.mm"
include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "cdif.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cuni.mm"
include "wi.mm"
include "w3a.mm"
include "wa.mm"
include "cfi.mm"
include "id.mm"
include "elin1d.mm"
include "ispisys.mm"
include "sylib.mm"
include "simpld.mm"
include "elpwid.mm"
include "c0.mm"
include "dif0.mm"
include "wdisj.mm"
include "elin2d.mm"
include "isldsys.mm"
include "simprd.mm"
include "simp2d.mm"
include "simp1d.mm"
include "wceq.mm"
include "difeq2.mm"
include "eqidd.mm"
include "eleq12d.mm"
include "rspcv.mm"
include "syl.mm"
include "mpd.mm"
include "syl5eqelr.mm"
include "unieq.mm"
include "uni0.mm"
include "syl6eq.mm"
include "adantl.mm"
include "ad3antrrr.mm"
include "eqeltrd.mm"
include "wne.mm"
include "cn.mm"
include "wfo.mm"
include "csdm.mm"
include "wex.mm"
include "vex.mm"
include "0sdom.mm"
include "biimpri.mm"
include "cen.mm"
include "simplr.mm"
include "nnenom.mm"
include "ensymi.mm"
include "domentr.mm"
include "sylancl.mm"
include "fodomr.mm"
include "syl2anc.mm"
include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "ciun.mm"
include "fveq2.mm"
include "iundisj.mm"
include "crn.mm"
include "wfn.mm"
include "fofn.mm"
include "fniunfv.mm"
include "forn.mm"
include "unieqd.mm"
include "eqtrd.mm"
include "syl5eqr.mm"
include "cmpt.mm"
include "cvv.mm"
include "fvex.mm"
include "difexg.mm"
include "ax-mp.mm"
include "dfiun3.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfel.mm"
include "nfan.mm"
include "simpr.mm"
include "nfiu1.mm"
include "nfdif.mm"
include "nfmpt.mm"
include "nfeq.mm"
include "ad7antr.mm"
include "simp-4r.mm"
include "wf.mm"
include "fof.mm"
include "ad4antlr.mm"
include "ffvelrnd.mm"
include "sseldd.mm"
include "cfn.mm"
include "fzofi.mm"
include "a1i.mm"
include "adantr.mm"
include "fzossnn.mm"
include "sselda.mm"
include "sigapildsyslem.mm"
include "wrex.mm"
include "eqid.mm"
include "elrnmpti.mm"
include "r19.29af.mm"
include "ex.mm"
include "ssrdv.mm"
include "wb.mm"
include "nnex.mm"
include "mptex.mm"
include "rnex.mm"
include "elpwg.mm"
include "sylibr.mm"
include "simp3d.mm"
include "ad4antr.mm"
include "nnct.mm"
include "mptct.mm"
include "rnct.mm"
include "mp1i.mm"
include "iundisj2.mm"
include "disjrnmpt.mm"
include "breq1.mm"
include "disjeq1.mm"
include "anbi12d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "imp.mm"
include "syl22anc.mm"
include "syl5eqel.mm"
include "eqeltrrd.mm"
include "exlimddv.mm"
include "pm2.61dane.mm"
include "ralrimiva.mm"
include "3jca.mm"
include "jca.mm"
include "issiga.mm"
include "ssriv.mm"
include "eqssi.mm"

theorem sigapildsys
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cL: class L
  let cO: class O
  let vs: setvar s
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let vt: setvar t
  let vz: setvar z
  assume dynkin.p: |- P = { s e. ~P ~P O | ( fi ` s ) C_ s }
  assume dynkin.l: |- L = { s e. ~P ~P O | ( (/) e. s /\ A. x e. s ( O \ x ) e. s /\ A. x e. ~P s ( ( x ~<_ _om /\ Disj_ y e. x y ) -> U. x e. s ) ) }

  disjoint s x
  disjoint s y
  disjoint x y
  disjoint L x
  disjoint L y
  disjoint O s
  disjoint O x
  disjoint P x
  disjoint P y
  disjoint f i
  disjoint f n
  disjoint f s
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint i n
  disjoint i s
  disjoint i t
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint n s
  disjoint n t
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint s t
  disjoint s z
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint x z
  disjoint y z
  disjoint L f
  disjoint L i
  disjoint L n
  disjoint L t
  disjoint O t
  disjoint P f
  disjoint P i
  disjoint P n
  disjoint P t
  assert |- ( sigAlgebra ` O ) = ( P i^i L )

  proof
    cO
    csiga
    cfv
    #
    cP
    cL
    cin
    #
    @0
    cP
    cL
    cP
    cO
    vs
    dynkin.p
    sigapisys
    vx
    vy
    cL
    cO
    vs
    dynkin.l
    sigaldsys
    ssini
    vt
    @1
    @0
    vt
    cv
    #
    @1
    wcel
    #
    @2
    cO
    cpw
    #
    wss
    #
    cO
    @2
    wcel
    #
    cO
    vx
    cv
    #
    cdif
    #
    @2
    wcel
    #
    vx
    @2
    wral
    #
    @7
    com
    cdom
    wbr
    #
    @7
    cuni
    #
    @2
    wcel
    #
    wi
    #
    vx
    @2
    cpw
    #
    wral
    #
    w3a
    #
    wa
    #
    @2
    @0
    wcel
    #
    @3
    @5
    @17
    @3
    @2
    @4
    @3
    @2
    @4
    cpw
    wcel
    #
    @2
    cfi
    cfv
    @2
    wss
    #
    @3
    @2
    cP
    wcel
    @20
    @21
    wa
    @3
    cP
    cL
    @2
    @3
    id
    #
    elin1d
    cP
    @2
    cO
    vs
    dynkin.p
    ispisys
    sylib
    simpld
    elpwid
    @3
    @6
    @10
    @16
    @3
    cO
    cO
    c0
    cdif
    #
    @2
    cO
    dif0
    @3
    @10
    @23
    @2
    wcel
    #
    @3
    c0
    @2
    wcel
    #
    @10
    @11
    vy
    @7
    vy
    cv
    #
    wdisj
    #
    wa
    #
    @13
    wi
    #
    vx
    @15
    wral
    #
    @3
    @20
    @25
    @10
    @30
    w3a
    #
    @3
    @2
    cL
    wcel
    @20
    @31
    wa
    @3
    cP
    cL
    @2
    @22
    elin2d
    vx
    vy
    @2
    cL
    cO
    vs
    dynkin.l
    isldsys
    sylib
    simprd
    #
    simp2d
    #
    @3
    @25
    @10
    @24
    wi
    @3
    @25
    @10
    @30
    @32
    simp1d
    #
    @9
    @24
    vx
    c0
    @2
    @7
    c0
    wceq
    #
    @8
    @23
    @2
    @2
    @7
    c0
    cO
    difeq2
    @35
    @2
    eqidd
    eleq12d
    rspcv
    syl
    mpd
    syl5eqelr
    @33
    @3
    @14
    vx
    @15
    @3
    @7
    @15
    wcel
    #
    wa
    #
    @11
    @13
    @37
    @11
    wa
    #
    @13
    @7
    c0
    @38
    @35
    wa
    @12
    c0
    @2
    @35
    @12
    c0
    wceq
    @38
    @35
    @12
    c0
    cuni
    c0
    @7
    c0
    unieq
    uni0
    syl6eq
    adantl
    @3
    @25
    @36
    @11
    @35
    @34
    ad3antrrr
    eqeltrd
    @38
    @7
    c0
    wne
    #
    wa
    #
    cn
    @7
    vf
    cv
    #
    wfo
    #
    @13
    vf
    @40
    c0
    @7
    csdm
    wbr
    #
    @7
    cn
    cdom
    wbr
    #
    @42
    vf
    wex
    @39
    @43
    @38
    @43
    @39
    @7
    vx
    vex
    0sdom
    biimpri
    adantl
    @40
    @11
    com
    cn
    cen
    wbr
    @44
    @37
    @11
    @39
    simplr
    cn
    com
    nnenom
    ensymi
    @7
    com
    cn
    domentr
    sylancl
    cn
    @7
    vf
    fodomr
    syl2anc
    @40
    @42
    wa
    #
    vn
    cn
    vn
    cv
    #
    @41
    cfv
    #
    vi
    c1
    @46
    cfzo
    co
    #
    vi
    cv
    #
    @41
    cfv
    #
    ciun
    #
    cdif
    #
    ciun
    #
    @12
    @2
    @42
    @53
    @12
    wceq
    @40
    @42
    @53
    vn
    cn
    @47
    ciun
    #
    @12
    @47
    @50
    vi
    vn
    @46
    @49
    @41
    fveq2
    #
    iundisj
    @42
    @54
    @41
    crn
    #
    cuni
    #
    @12
    @42
    @41
    cn
    wfn
    @54
    @57
    wceq
    cn
    @7
    @41
    fofn
    vn
    cn
    @41
    fniunfv
    syl
    @42
    @56
    @7
    cn
    @7
    @41
    forn
    unieqd
    eqtrd
    syl5eqr
    adantl
    @45
    @53
    vn
    cn
    @52
    cmpt
    #
    crn
    #
    cuni
    #
    @2
    vn
    cn
    @52
    @47
    cvv
    wcel
    @52
    cvv
    wcel
    @46
    @41
    fvex
    @47
    @51
    cvv
    difexg
    ax-mp
    #
    dfiun3
    @45
    @59
    @15
    wcel
    #
    @30
    @59
    com
    cdom
    wbr
    #
    vy
    @59
    @26
    wdisj
    #
    @60
    @2
    wcel
    #
    @45
    @59
    @2
    wss
    #
    @62
    @45
    vy
    @59
    @2
    @45
    @26
    @59
    wcel
    #
    @26
    @2
    wcel
    #
    @45
    @67
    wa
    #
    @26
    @52
    wceq
    #
    @68
    vn
    cn
    @45
    @67
    vn
    @45
    vn
    nfv
    vn
    @26
    @59
    vn
    @26
    nfcv
    vn
    @58
    vn
    cn
    @52
    nfmpt1
    nfrn
    nfel
    nfan
    @69
    @46
    cn
    wcel
    #
    wa
    #
    @70
    wa
    #
    @26
    @52
    @2
    @72
    @70
    simpr
    @73
    vx
    vy
    vt
    @47
    @50
    cP
    vi
    cL
    @48
    cO
    vs
    dynkin.p
    dynkin.l
    @72
    @70
    vi
    @69
    @71
    vi
    @45
    @67
    vi
    @45
    vi
    nfv
    vi
    @26
    @59
    vi
    @26
    nfcv
    #
    vi
    @58
    vi
    vn
    cn
    @52
    vi
    cn
    nfcv
    vi
    @47
    @51
    vi
    @47
    nfcv
    vi
    @48
    @50
    nfiu1
    nfdif
    #
    nfmpt
    nfrn
    nfel
    nfan
    @71
    vi
    nfv
    nfan
    vi
    @26
    @52
    @74
    @75
    nfeq
    nfan
    @3
    @3
    @36
    @11
    @39
    @42
    @67
    @71
    @70
    @22
    ad7antr
    @73
    @7
    @2
    @47
    @73
    @7
    @2
    @45
    @36
    @67
    @71
    @70
    @3
    @36
    @11
    @39
    @42
    simp-4r
    ad3antrrr
    elpwid
    #
    @73
    cn
    @7
    @46
    @41
    @42
    cn
    @7
    @41
    wf
    #
    @40
    @67
    @71
    @70
    cn
    @7
    @41
    fof
    ad4antlr
    #
    @69
    @71
    @70
    simplr
    ffvelrnd
    sseldd
    @48
    cfn
    wcel
    @73
    c1
    @46
    fzofi
    a1i
    @73
    @49
    @48
    wcel
    #
    wa
    #
    @7
    @2
    @50
    @73
    @7
    @2
    wss
    @79
    @76
    adantr
    @80
    cn
    @7
    @49
    @41
    @73
    @77
    @79
    @78
    adantr
    @73
    @48
    cn
    @49
    @48
    cn
    wss
    @73
    @46
    fzossnn
    a1i
    sselda
    ffvelrnd
    sseldd
    sigapildsyslem
    eqeltrd
    @69
    @67
    @70
    vn
    cn
    wrex
    @45
    @67
    simpr
    vn
    cn
    @52
    @26
    @58
    @58
    eqid
    @61
    elrnmpti
    sylib
    r19.29af
    ex
    ssrdv
    @59
    cvv
    wcel
    @62
    @66
    wb
    @58
    vn
    cn
    @52
    nnex
    mptex
    rnex
    @59
    @2
    cvv
    elpwg
    ax-mp
    sylibr
    @3
    @30
    @36
    @11
    @39
    @42
    @3
    @25
    @10
    @30
    @32
    simp3d
    ad4antr
    @58
    com
    cdom
    wbr
    #
    @63
    @45
    cn
    com
    cdom
    wbr
    @81
    nnct
    vn
    cn
    @52
    mptct
    ax-mp
    @58
    rnct
    mp1i
    vn
    cn
    @52
    wdisj
    @64
    @45
    @47
    @50
    vi
    vn
    @55
    iundisj2
    vn
    vy
    cn
    @52
    disjrnmpt
    mp1i
    @62
    @30
    wa
    @63
    @64
    wa
    #
    @65
    @62
    @30
    @82
    @65
    wi
    #
    @29
    @83
    vx
    @59
    @15
    @7
    @59
    wceq
    #
    @28
    @82
    @13
    @65
    @84
    @11
    @63
    @27
    @64
    @7
    @59
    com
    cdom
    breq1
    vy
    @7
    @59
    @26
    disjeq1
    anbi12d
    @84
    @12
    @60
    @2
    @7
    @59
    unieq
    eleq1d
    imbi12d
    rspcv
    imp
    imp
    syl22anc
    syl5eqel
    eqeltrrd
    exlimddv
    pm2.61dane
    ex
    ralrimiva
    3jca
    jca
    @2
    cvv
    wcel
    @19
    @18
    wb
    vt
    vex
    vx
    @2
    cO
    issiga
    ax-mp
    sylibr
    ssriv
    eqssi
end

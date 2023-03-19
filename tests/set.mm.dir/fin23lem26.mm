include "cv.mm"
include "com.mm"
include "wcel.mm"
include "wss.mm"
include "cfn.mm"
include "wn.mm"
include "wa.mm"
include "cin.mm"
include "cen.mm"
include "wbr.mm"
include "wrex.mm"
include "c0.mm"
include "csuc.mm"
include "wceq.mm"
include "breq2.mm"
include "rexbidv.mm"
include "weq.mm"
include "word.mm"
include "wne.mm"
include "ordom.mm"
include "a1i.mm"
include "simpl.mm"
include "0fin.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "necon3bi.mm"
include "adantl.mm"
include "tz7.5.mm"
include "syl3anc.mm"
include "en0.mm"
include "incom.mm"
include "eqeq1i.mm"
include "bitri.mm"
include "rexbii.mm"
include "sylibr.mm"
include "wi.mm"
include "cdif.mm"
include "cint.mm"
include "con0.mm"
include "simplrl.mm"
include "omsson.mm"
include "syl6ss.mm"
include "ssdifssd.mm"
include "simplr.mm"
include "ssel2.mm"
include "onfin2.mm"
include "inss2.mm"
include "eqsstri.mm"
include "peano2.mm"
include "sseldi.mm"
include "syl.mm"
include "adantlr.mm"
include "ssfi.mm"
include "ex.mm"
include "mtod.mm"
include "ssdif0.mm"
include "necon3bbii.mm"
include "sylib.mm"
include "ad2ant2lr.mm"
include "onint.mm"
include "syl2anc.mm"
include "eldifad.mm"
include "csn.mm"
include "cun.mm"
include "simprr.mm"
include "cvv.mm"
include "vex.mm"
include "en2sn.mm"
include "mp2an.mm"
include "simprl.mm"
include "sseldd.mm"
include "nnord.mm"
include "wel.mm"
include "ordirr.mm"
include "inss1.mm"
include "sseli.mm"
include "nsyl.mm"
include "disjsn.mm"
include "ad2antrr.mm"
include "unen.mm"
include "syl22anc.mm"
include "wb.mm"
include "ordsuc.mm"
include "adantrr.mm"
include "w3a.mm"
include "simp2.mm"
include "simpl1.mm"
include "simpr.mm"
include "eldifd.mm"
include "onnmin.mm"
include "syl6an.mm"
include "con4d.mm"
include "imp.mm"
include "simp3.mm"
include "ordsucss.mm"
include "sscond.mm"
include "intss.mm"
include "simpl2.mm"
include "ordelon.mm"
include "sylan.mm"
include "onmindif.mm"
include "impbida.mm"
include "df-suc.mm"
include "eleq2i.mm"
include "syl6bb.mm"
include "expr.mm"
include "pm5.32rd.mm"
include "elin.mm"
include "3bitr4g.mm"
include "eqrdv.mm"
include "indir.mm"
include "syl6eq.mm"
include "snssi.mm"
include "df-ss.mm"
include "uneq2d.mm"
include "ad2antrl.mm"
include "eqtrd.mm"
include "3brtr4d.mm"
include "ineq1.mm"
include "breq1d.mm"
include "rspcev.mm"
include "rexlimdvaa.mm"
include "cbvrexv.mm"
include "syl6ib.mm"
include "finds2.mm"
include "impcom.mm"

theorem fin23lem26
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let va: setvar a
  let vb: setvar b
  let cC: class C

  disjoint i j
  disjoint S i
  disjoint S j
  disjoint a i
  disjoint b i
  disjoint a j
  disjoint b j
  disjoint a b
  disjoint S a
  disjoint S b
  disjoint C a
  disjoint C b
  assert |- ( ( ( S C_ _om /\ -. S e. Fin ) /\ i e. _om ) -> E. j e. S ( j i^i S ) ~~ i )

  proof
    vi
    cv
    #
    com
    wcel
    cS
    com
    wss
    #
    cS
    cfn
    wcel
    #
    wn
    #
    wa
    #
    vj
    cv
    #
    cS
    cin
    #
    @0
    cen
    wbr
    #
    vj
    cS
    wrex
    #
    @8
    @6
    c0
    cen
    wbr
    #
    vj
    cS
    wrex
    #
    @6
    va
    cv
    #
    cen
    wbr
    #
    vj
    cS
    wrex
    #
    @6
    @11
    csuc
    #
    cen
    wbr
    #
    vj
    cS
    wrex
    #
    @4
    vi
    va
    @0
    c0
    wceq
    @7
    @9
    vj
    cS
    @0
    c0
    @6
    cen
    breq2
    rexbidv
    vi
    va
    weq
    @7
    @12
    vj
    cS
    @0
    @11
    @6
    cen
    breq2
    rexbidv
    @0
    @14
    wceq
    @7
    @15
    vj
    cS
    @0
    @14
    @6
    cen
    breq2
    rexbidv
    @4
    cS
    @5
    cin
    #
    c0
    wceq
    #
    vj
    cS
    wrex
    #
    @10
    @4
    com
    word
    #
    @1
    cS
    c0
    wne
    #
    @19
    @20
    @4
    ordom
    a1i
    @1
    @3
    simpl
    @3
    @21
    @1
    @2
    cS
    c0
    cS
    c0
    wceq
    @2
    c0
    cfn
    wcel
    0fin
    cS
    c0
    cfn
    eleq1
    mpbiri
    necon3bi
    adantl
    vj
    com
    cS
    tz7.5
    syl3anc
    @9
    @18
    vj
    cS
    @9
    @6
    c0
    wceq
    @18
    @6
    en0
    @6
    @17
    c0
    @5
    cS
    incom
    eqeq1i
    bitri
    rexbii
    sylibr
    @11
    com
    wcel
    #
    @4
    @13
    @16
    wi
    @22
    @4
    wa
    #
    @13
    vb
    cv
    #
    cS
    cin
    #
    @14
    cen
    wbr
    #
    vb
    cS
    wrex
    #
    @16
    @23
    @12
    @27
    vj
    cS
    @23
    @5
    cS
    wcel
    #
    @12
    wa
    #
    wa
    #
    cS
    @5
    csuc
    #
    cdif
    #
    cint
    #
    cS
    wcel
    @33
    cS
    cin
    #
    @14
    cen
    wbr
    #
    @27
    @30
    @33
    cS
    @31
    @30
    @32
    con0
    wss
    #
    @32
    c0
    wne
    #
    @33
    @32
    wcel
    @30
    cS
    con0
    @31
    @30
    cS
    com
    con0
    @22
    @1
    @3
    @29
    simplrl
    #
    omsson
    syl6ss
    ssdifssd
    @4
    @28
    @37
    @22
    @12
    @4
    @28
    wa
    #
    cS
    @31
    wss
    #
    wn
    @37
    @39
    @40
    @2
    @1
    @3
    @28
    simplr
    @39
    @31
    cfn
    wcel
    #
    @40
    @2
    wi
    @1
    @28
    @41
    @3
    @1
    @28
    wa
    @5
    com
    wcel
    #
    @41
    cS
    com
    @5
    ssel2
    @42
    com
    cfn
    @31
    com
    con0
    cfn
    cin
    cfn
    onfin2
    con0
    cfn
    inss2
    eqsstri
    @5
    peano2
    sseldi
    syl
    adantlr
    @41
    @40
    @2
    @31
    cS
    ssfi
    ex
    syl
    mtod
    @40
    @32
    c0
    cS
    @31
    ssdif0
    necon3bbii
    sylib
    ad2ant2lr
    @32
    onint
    syl2anc
    eldifad
    @30
    @6
    @5
    csn
    #
    cun
    #
    @11
    @11
    csn
    #
    cun
    #
    @34
    @14
    cen
    @30
    @12
    @43
    @45
    cen
    wbr
    #
    @6
    @43
    cin
    c0
    wceq
    #
    @11
    @45
    cin
    c0
    wceq
    #
    @44
    @46
    cen
    wbr
    @23
    @28
    @12
    simprr
    @47
    @30
    @5
    cvv
    wcel
    @11
    cvv
    wcel
    @47
    vj
    vex
    va
    vex
    @5
    @11
    cvv
    cvv
    en2sn
    mp2an
    a1i
    @30
    @5
    word
    #
    @48
    @30
    @42
    @50
    @30
    cS
    com
    @5
    @38
    @23
    @28
    @12
    simprl
    sseldd
    @5
    nnord
    syl
    #
    @50
    @5
    @6
    wcel
    #
    wn
    @48
    @50
    vj
    vj
    wel
    @52
    @5
    ordirr
    @6
    @5
    @5
    @5
    cS
    inss1
    sseli
    nsyl
    @6
    @5
    disjsn
    sylibr
    syl
    @22
    @49
    @4
    @29
    @22
    va
    va
    wel
    wn
    #
    @49
    @22
    @11
    word
    @53
    @11
    nnord
    @11
    ordirr
    syl
    @11
    @11
    disjsn
    sylibr
    ad2antrr
    @6
    @11
    @43
    @45
    unen
    syl22anc
    @30
    @34
    @6
    @43
    cS
    cin
    #
    cun
    #
    @44
    @30
    @34
    @5
    @43
    cun
    #
    cS
    cin
    #
    @55
    @30
    vb
    @34
    @57
    @30
    @24
    @33
    wcel
    #
    @24
    cS
    wcel
    #
    wa
    @24
    @56
    wcel
    #
    @59
    wa
    @24
    @34
    wcel
    @24
    @57
    wcel
    @30
    @59
    @58
    @60
    @23
    @29
    @59
    @58
    @60
    wb
    @23
    @29
    @59
    wa
    #
    wa
    #
    @58
    @24
    @31
    wcel
    #
    @60
    @62
    @59
    cS
    con0
    wss
    #
    @31
    word
    #
    @58
    @63
    wb
    @23
    @29
    @59
    simprr
    @62
    cS
    com
    con0
    @22
    @1
    @3
    @61
    simplrl
    omsson
    syl6ss
    @23
    @29
    @65
    @59
    @30
    @50
    @65
    @51
    @5
    ordsuc
    sylib
    adantrr
    @59
    @64
    @65
    w3a
    #
    @58
    @63
    @66
    @58
    @63
    @66
    @63
    @58
    @66
    @36
    @63
    wn
    #
    @24
    @32
    wcel
    #
    @58
    wn
    @66
    cS
    con0
    @31
    @59
    @64
    @65
    simp2
    ssdifssd
    @66
    @67
    @68
    @66
    @67
    wa
    @24
    cS
    @31
    @59
    @64
    @65
    @67
    simpl1
    @66
    @67
    simpr
    eldifd
    ex
    @32
    @24
    onnmin
    syl6an
    con4d
    imp
    @66
    @63
    wa
    #
    cS
    @24
    csuc
    #
    cdif
    #
    cint
    #
    @33
    @24
    @69
    @32
    @71
    wss
    @72
    @33
    wss
    @69
    @70
    @31
    cS
    @66
    @63
    @70
    @31
    wss
    #
    @66
    @65
    @63
    @73
    wi
    @59
    @64
    @65
    simp3
    #
    @24
    @31
    ordsucss
    syl
    imp
    sscond
    @32
    @71
    intss
    syl
    @69
    @64
    @24
    con0
    wcel
    #
    @24
    @72
    wcel
    @59
    @64
    @65
    @63
    simpl2
    @66
    @65
    @63
    @75
    @74
    @31
    @24
    ordelon
    sylan
    cS
    @24
    onmindif
    syl2anc
    sseldd
    impbida
    syl3anc
    @31
    @56
    @24
    @5
    df-suc
    eleq2i
    syl6bb
    expr
    pm5.32rd
    @24
    @33
    cS
    elin
    @24
    @56
    cS
    elin
    3bitr4g
    eqrdv
    @5
    @43
    cS
    indir
    syl6eq
    @28
    @55
    @44
    wceq
    @23
    @12
    @28
    @54
    @43
    @6
    @28
    @43
    cS
    wss
    @54
    @43
    wceq
    @5
    cS
    snssi
    @43
    cS
    df-ss
    sylib
    uneq2d
    ad2antrl
    eqtrd
    @14
    @46
    wceq
    @30
    @11
    df-suc
    a1i
    3brtr4d
    @26
    @35
    vb
    @33
    cS
    @24
    @33
    wceq
    @25
    @34
    @14
    cen
    @24
    @33
    cS
    ineq1
    breq1d
    rspcev
    syl2anc
    rexlimdvaa
    @26
    @15
    vb
    vj
    cS
    vb
    vj
    weq
    @25
    @6
    @14
    cen
    @24
    @5
    cS
    ineq1
    breq1d
    cbvrexv
    syl6ib
    ex
    finds2
    impcom
end
